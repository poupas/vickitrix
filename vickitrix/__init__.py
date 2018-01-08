#!/usr/bin/env python
"""
vickitrix

Checks tweets using http://www.tweepy.org/ and
uses rules specified in file to make market trades on GDAX using
https://github.com/danpaquin/GDAX-Python. Default rules are stored in 
rules/vicki.py and follow the tweets of @vickicryptobot.
"""
from __future__ import print_function

import sys
import os
import errno
import time
import argparse
import getpass
import base64
import json

from _collections import defaultdict

# For 2-3 compatibility
try:
    input = raw_input
except NameError:
    pass

_help_intro = """vickitrix allows users to base GDAX trades on tweets."""
_key_derivation_iterations = 5000

try:
    import gdax
except ImportError as e:
    e.message = (
         'vickitrix requires GDAX-Python. Install it with "pip install gdax".'
        )
    raise

try:
    from twython import  Twython, TwythonError
except ImportError as e:
    e.message = (
            'vickitrix requires Twython. Install it with '
            '"pip install twython".'
        )
    raise

try:
    from Crypto.Cipher import AES
    from Crypto.Protocol import KDF
    from Crypto import Random
except ImportError as e:
    e.message = (
        'vickitrix requires PyCrypto. Install it with '
        '"pip install pycrypto".'
    )
    raise


# In case user wants to use regular expressions on conditions/funds
import re
import logging

logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO)
log = logging.getLogger(__name__)
log.setLevel(logging.DEBUG)


def help_formatter(prog):
    """ So formatter_class's max_help_position can be changed. """
    return argparse.HelpFormatter(prog, max_help_position=40)


def prettify_dict(rule):
    """ Prettifies printout of dictionary as string.

        rule: rule

        Return value: rule string
    """
    return json.dumps(rule, sort_keys=False,
                        indent=4, separators=(',', ': '))


def get_balance(gdax_client, status_update=False):
    """ Retrieve dough in user accounts

        gdax_client: instance of gdax.AuthenticatedClient
        status_update: True iff status update should be printed

        Return value: dictionary mapping currency to account information
    """
    balance = {}
    for account in gdax_client.get_accounts():
        balance[account['currency']] = account['available']
    if status_update:
        balance_str = ', '.join('%s: %s' % (p, a) for p, a in balance.items())
        log.info('Current balance in wallet: %s' % balance_str)
    return balance


def relevant_tweet(tweet, rule, balance):
    if (
        # Check if this is a user we are following
        ((not rule['handles']) or
         ('user' in tweet and tweet['user']['screen_name'].lower() in rule['handles']))

        and

        # Check if the tweet text matches any defined condition
        ((not rule['keywords']) or
         any([keyword in tweet['text'].lower() for keyword in rule['keywords']]))

        and

        eval(rule['condition'].format(tweet='tweet["text"]',available=balance))):

        # Check if this is an RT or reply
        if (('retweeted_status' in tweet and tweet['retweeted_status']) or
                tweet['in_reply_to_status_id'] or
                tweet['in_reply_to_status_id_str'] or
                tweet['in_reply_to_user_id'] or
                tweet['in_reply_to_user_id_str'] or
                tweet['in_reply_to_screen_name']):

            return False

        return True

    return False


def twitter_handles_to_userids(twitter, handles):
    ids_map = {}

    for handle in handles:
        try:
            ids_map[handle] = twitter.show_user(screen_name=handle)['id_str']
        except TwythonError as e:
            if 'User not found' in e.message:
                log.warning('Handle %s not found; skipping rule...' % handle)
            else:
                raise

    if not ids_map:
        raise RuntimeError('No followable Twitter handles found in rules!')

    return ids_map


class State:
    def __init__(self, path):
        self.path = path
        self.d = self._load()

    def _load(self):
        try:
            with open(self.path, 'r') as fp:
                return json.load(fp)
        except (ValueError, IOError, TypeError):
            log.warning("Could not load state from '%s'. Creating new..." %
                        self.path)
            return {
                'twitter': {
                    'pairs': {},
                },
                'gdax': {
                    'pairs': {},
                },
            }

    def save(self):
        with open(self.path, 'w', encoding='ascii') as fp:
            json.dump(self.d, fp)


def new_order(rule, order, tweet):
    ttl_s = int(rule.get('ttl_seconds', 60))
    retries = int(rule.get('retries', 1))
    now = int(time.time())
    return {
        'gdax_order': order,
        'pair': order['product_id'],
        'side': order['side'],
        'handle': tweet['user']['screen_name'].lower(),
        'id': tweet['id_str'],
        'tries_left': retries,
        'market_fallback': rule.get('market_fallback', False),
        'status': 'new',
        'gdax_id': None,
        'ttl_s': ttl_s,
        'try_expires': None,
        'expires': now + ttl_s * retries
    }


class TradingStateMachine:
    """ Trades on GDAX based on tweets. """

    def __init__(self, rules, gdax_client, twitter_client, handles, state,
                 sleep_time=0.5):
        self.rules = rules
        self.gdax = gdax_client
        self.twitter = twitter_client
        self.handles = handles
        self.state_obj = state
        self.state = state.d
        self.sleep_time = sleep_time
        self.available = get_balance(self.gdax, status_update=False)
        self.public_client = gdax.PublicClient() # for product order book

    def _run(self):
        twitter_state = self.state['twitter']
        gdax_state = self.state['gdax']
        ids_map = twitter_handles_to_userids(self.twitter, self.handles)
        tweets = []

        # Refresh Twitter status
        for handle, uid in ids_map.items():
            try:
                latest_tweet = twitter_state[handle]['id']
            except KeyError:
                latest_tweet = None

            tweets += self.twitter.get_user_timeline(
                user_id=uid, exclude_replies=True, since_id=latest_tweet)

        orders = {}
        for tweet in tweets:
            self._paper_trade(tweet, orders)

        for o in orders.values():
            # Update Twitter state
            self._update_state(
                twitter_state, o['handle'], o['id'], o['pair'], o['side'])

            # Make sure that GDAX state is initialized
            self._update_state(
                gdax_state, o['handle'], o['id'], o['pair'], None, order=o)

        # Check if there is any order pending.
        for pair in gdax_state['pairs'].values():
            order = pair['order']

            if order['status'] in ('settled', 'expired'):
                continue

            # Check if the pending order is still valid
            now = int(time.time())
            if order['status'] == 'pending':
                r = self.gdax.get_order(order['gdax_id'])
                if r.get('status') in ('done', 'settled'):
                    order['status'] = 'settled'
                    log.info("Order completed!: %s", order)
                    continue
                elif now < order['try_expires']:
                    log.debug("Pending order is still valid: %s", order)
                    continue

            if order['tries_left'] > 0 and now < order['expires']:
                order['tries_left'] -= 1
                order['try_expires'] = now + order['ttl_s']
                o = self._add_order(order)
                pair['side'] = o['side']
            else:
                fallback = order['market_fallback']
                if fallback and order['gdax_order']['type'] == 'limit':
                    order['gdax_order']['type'] = 'market'
                    order['tries_left'] = 1
                    order['try_expires'] = now + order['ttl_s']
                    order['expires'] = order['try_expires']
                else:
                    order['status'] = 'expired'

        self.state_obj.save()

    def _order_waiting(self, order):
        if order['status'] != 'pending':
            return False

        r = self.gdax.get_order(order['gdax_id'])
        assert(r is not None)
        if 'id' not in r:
            return False

        log.info("Found an order waiting: %s", r)
        return r['status'] != 'settled'

    def _update_state(self, state, handle, new_id, pair, side, order=None):
        try:
            handle_id = state[handle]['id']
            pair_id = state['pairs'][pair]['id']
        except KeyError:
            if handle not in state:
                state[handle] = {
                    'id': new_id
                }

            if pair not in state['pairs']:
                state['pairs'][pair] = {
                    'side': side,
                    'id': new_id
                }
                if order is not None:
                    state['pairs'][pair]['order'] = order

            handle_id = state[handle]['id']
            pair_id = state['pairs'][pair]['id']

        if int(new_id) > int(handle_id):
            state[handle]['id'] = new_id

        if int(new_id) > int(pair_id):
            state['pairs'][pair]['id'] = new_id
            state['pairs'][pair]['side'] = side
            state['pairs'][pair]['order'] = order

    def _get_orders(self, tweet, rule):
        orders = []
        for order in rule['orders']:
            orders.append(new_order(rule, order, tweet))
        return orders

    def _add_order(self, order):
        gdax_order = order['gdax_order']
        # Ensure that there is no pending order for this pair.
        if order['status'] == 'pending':
            reply = self.gdax.cancel_order(order['gdax_id'])
            if reply is None or 'error' in reply:
                log.error("Could not cancel order: %s", order['gdax_id'])
                order['status'] = 'error'
                return order

        self.available = get_balance(self.gdax, status_update=True)
        order_book = self.public_client.get_product_order_book(order['pair'])

        inside_bid = order_book['bids'][0][0]
        inside_ask = order_book['asks'][0][0]

        not_enough = False
        for money in ['size', 'funds', 'price']:
            try:
                '''If the hundredths rounds down to zero,
                ain't enough'''
                gdax_order[money] = str(eval(
                    gdax_order[money].format(
                        tweet='tweet.text',
                        available=self.available,
                        inside_bid=inside_bid,
                        inside_ask=inside_ask
                    )
                ))
                not_enough = int(float(gdax_order[money]) * 100) == 0

            except KeyError:
                pass

        log.info('Placing order: %s' % prettify_dict(gdax_order))
        if not_enough:
            log.warning(
                'One of {"price", "funds", "size"} is zero! '
                'Order not placed.')
            order['status'] = 'error'
            return order

        if order['side'] == 'buy':
            r = self.gdax.buy(**gdax_order)
        else:
            assert order['side'] == 'sell'
            r = self.gdax.sell(**gdax_order)

        log.info('Order placed.')
        time.sleep(self.sleep_time)

        if 'id' in r:
            order['gdax_id'] = r['id']
            order['status'] = r['status']
        else:
            order['status'] = 'error'

        return order

    def _paper_trade(self, tweet, orders):
        log.debug("Got the following tweet: %s" % tweet['text'])

        for rule in self.rules:
            if not relevant_tweet(tweet, rule, self.available):
                continue

            # Relevant tweet. Do something with it...
            log.info("Tweet rule match || @ %s: %s" %
                     (tweet['user']['screen_name'], tweet['text']))

            new_orders = self._get_orders(tweet, rule)
            for o in new_orders:
                if (o['pair'] not in orders or
                        int(o['id']) > int(orders[o['pair']]['id'])):
                    log.info("Adding order [%s] to pending orders list...",
                             o['gdax_order'])
                    orders[o['pair']] = o
                else:
                    log.warning("Ignoring order [%s]; newer order exists.",
                                o['gdax_order'])

    def run(self):
        while True:
            self._run()
            log.debug("Sleeping...")
            time.sleep(120)


def go():
    """ Entry point """
    # Print file's docstring if -h is invoked
    parser = argparse.ArgumentParser(description=_help_intro, 
                formatter_class=help_formatter)
    subparsers = parser.add_subparsers(help=(
                'subcommands; add "-h" or "--help" '
                'after a subcommand for its parameters'),
                dest='subparser_name'
            )
    config_parser = subparsers.add_parser(
                            'configure',
                            help=(
                                'creates profile for storing keys/secrets; '
                                'all keys are stored in "{}".'.format(
                                        os.path.join(
                                            os.path.expanduser('~'),
                                            '.vickitrix',
                                            'config')
                                    )
                            )
                        )
    trade_parser = subparsers.add_parser(
                            'trade',
                            help='trades based on tweets'
                        )
    # Add command-line arguments
    trade_parser.add_argument('--profile', '-p', type=str, required=False,
            default='default',
            help='which profile to use for trading'
        )
    trade_parser.add_argument('--rules', '-r', type=str, required=False,
            default=os.path.join(os.path.dirname(os.path.realpath(__file__)),
                                    'rules', 'vicki.py'),
            help=('rules file; this is Python that sets the variable "rules" '
                  'to a list of dictionaries')
        )
    trade_parser.add_argument('--interval', '-i', type=float, required=False,
            default=905,
            help=('how long to wait (in s) before reattempting to connect '
                  'after getting rate-limited')
        )
    trade_parser.add_argument('--sleep', '-s', type=float, required=False,
            default=0.5,
            help='how long to wait (in s) after an order has been placed'
        )
    args = parser.parse_args()
    key_dir = os.path.join(os.path.expanduser('~'), '.vickitrix')
    if args.subparser_name == 'configure':
        try:
            os.makedirs(key_dir)
        except OSError as e:
            if e.errno != errno.EEXIST:
                raise
        # Grab and write all necessary credentials
        config_file = os.path.join(key_dir, 'config')
        print('Enter a name for a new profile (default): ', end='')
        profile_name = input()
        if not profile_name: profile_name = 'default'
        salt = Random.new().read(AES.block_size)
        key = KDF.PBKDF2(getpass.getpass((
                'Enter a password for this profile. The password will be used '
                'to generate a key so all GDAX/Twitter passcodes/secrets '
                'written to {} are further encoded with AES256. '
                'You will have to enter a profile\'s password every time you '
                'run "vickitrix trade": '
            ).format(config_file)), salt,
                dkLen=32, count=_key_derivation_iterations)
        previous_lines_to_write = []
        if os.path.exists(config_file):
            '''Have to check if the profile exists already. If it does, replace
            it. Assume the config file is under vickitrix's control and thus 
            has no errors; if the user chooses to mess it up, that's on
            them.'''
            with open(config_file, 'rU') as config_stream:
                line = config_stream.readline().rstrip('\n')
                while line:
                    if line[0] == '[' and line[-1] == ']':
                        if profile_name == line[1:-1]:
                            # Skip this profile
                            for _ in range(8): config_stream.readline()
                            line = config_stream.readline().rstrip('\n')
                            continue
                        previous_lines_to_write.append(line)
                        for _ in range(8):
                            previous_lines_to_write.append(
                                        config_stream.readline().rstrip('\n')
                                    )
                    line = config_stream.readline().rstrip('\n')
        with open(config_file, 'w') as config_stream:
            print(''.join(['[', profile_name, ']']), file=config_stream)
        # Now change permissions
        try:
            os.chmod(config_file, 0o600)
        except OSError as e:
            if e.errno == errno.EPERM:
                print >>sys.stderr, (
                        ('Warning: could not change permissions of '
                         '"{}" so it\'s readable/writable by only the '
                         'current user. If there are other users of this '
                         'system, they may be able to read your credentials '
                         'file.').format(
                                config_file
                            )
                    )
                raise
        with open(config_file, 'a') as config_stream:
            print(''.join(['Salt: ', base64.b64encode(salt).decode()]),
                    file=config_stream)
            for token in ['GDAX key', 'GDAX secret', 'GDAX passphrase',
                            'Twitter consumer key', 'Twitter consumer secret',
                            'Twitter access token key',
                            'Twitter access token secret']:
                if 'key' in token:
                    print(''.join(['Enter ', token, ': ']), end='')
                    '''Write it in plaintext if it's a public key; then the 
                    user can open the config file and know which keys are in 
                    use.'''
                    print(''.join([token, ': ', input()]),
                            file=config_stream)
                else:
                    # A warning to developers in a variable name
                    unencoded_and_not_to_be_written_to_disk = getpass.getpass(
                                        ''.join(['Enter ', token, ': '])
                                    )
                    iv = Random.new().read(AES.block_size)
                    cipher = AES.new(key, AES.MODE_CFB, iv)
                    print(''.join([
                            token,
                            ' (AES256-encrypted using profile password): ',
                            base64.b64encode(iv + cipher.encrypt(
                                unencoded_and_not_to_be_written_to_disk
                            )).decode()]), file=config_stream)
            for line in previous_lines_to_write:
                print(line, file=config_stream)
        print(('Configured profile "{}". Encrypted credentials have been '
               'stored in "{}". '
               'Now use the "trade" subcommand to '
               'trigger trades with new tweets.').format(
                        profile_name,
                        config_file
                    ))
    elif args.subparser_name == 'trade':
        # Set and check rules
        from imp import load_source
        try:
            rules = load_source('rules', args.rules).rules
        except IOError as e:
            e.message = 'Cannot find or access rules file "{}".'.format(
                                                                    args.rules
                                                                )
            raise
        import copy
        # Add missing keys so listener doesn't fail
        new_rules = copy.copy(rules)
        order_vocab = frozenset([
            'client_oid', 'type', 'side', 'product_id', 'stp',
            'price', 'size', 'time_in_force', 'cancel_after',
            'post_only', 'funds', 'overdraft_enabled', 'funding_amount',
        ])

        for i, rule in enumerate(rules):
            # Check 'condition'
            try:
                eval(rule['condition'].format(
                        tweet='"The rain in Spain stays mainly in the plain."',
                        available={
                            'ETH' : .01,
                            'USD' : .01,
                            'LTC' : .01,
                            'BTC' : .01
                        }
                    ))
            except KeyError:
                # 'condition' isn't required, so make default True
                new_rules[i]['condition'] = 'True'
            except:
                raise RuntimeError(''.join([
                        ('"condition" from the following rule in the file '
                         '"{}" could not be '
                         'evaluated; check the format '
                         'and try again: ').format(args.rules),
                        os.linesep, prettify_dict(rule)
                    ])
                )

            # Check handles and keywords
            if 'handles' not in rule and 'keywords' not in rule:
                raise RuntimeError(''.join([
                        ('A rule must have at least one of {{"handles", '
                         '"keywords"}}, but this rule from the file "{}" '
                         'doesn\'t:').format(args.rules),
                        os.linesep, prettify_dict(rule)
                    ])
                )
            if 'handles' not in rule:
                new_rules[i]['handles'] = []
            if 'keywords' not in rule:
                new_rules[i]['keywords'] = []
            new_rules[i]['handles'] = [
                    handle.lower() for handle in new_rules[i]['handles']
                ]
            new_rules[i]['keywords'] = [
                    keyword.lower() for keyword in new_rules[i]['keywords']
                ]
            '''Validate order; follow https://docs.gdax.com/#orders for 
            filling in default values.'''
            if 'orders' not in rule or not isinstance(rule['orders'], list):
                raise RuntimeError(''.join([
                        ('Every rule must have an "orders" list, but '
                         'this rule from the file "{}" doesn\'t:').format(
                        args.rules), os.linesep, prettify_dict(rule)
                    ])
                )
            for j, order in enumerate(rule['orders']):
                if not isinstance(order, dict):
                    raise RuntimeError(''.join([
                        ('Every order must be a dictionary, but order #{} '
                         'from this rule in the file "{}" isn\'t:').format(
                        j+1, args.rules), os.linesep, prettify_dict(rule)]))
                unrecognized_keys = [
                        key for key in order if key not in order_vocab
                    ]
                if unrecognized_keys:
                    raise RuntimeError(''.join([
                        'In the file "{}", the "order" key(s) '.format(
                            args.rules),
                        os.linesep, '[',
                        ', '.join(unrecognized_keys), ']', os.linesep,
                        ('are invalid yet present in order #{} of '
                         'the following rule:').format(j+1),
                        os.linesep, prettify_dict(rule)
                    ]))
                try:
                    if order['type'] not in ('limit', 'market', 'stop'):
                        raise RuntimeError(''.join([
                            ('An order\'s "type" must be one of {{"limit", '
                             '"market", "stop"}}, which order #{} in this '
                             'rule from the file "{}" doesn\'t '
                             'satisfy:').format(j+1, args.rules),
                            os.linesep, prettify_dict(rule)
                        ]))
                except KeyError:
                    # GDAX default is limit
                    new_rules[i]['orders'][j]['type'] = 'limit'
                if 'side' not in order:
                    raise RuntimeError(''.join([
                            ('An order must have a "side", but order #{} in '
                             'this rule from the file "{}" doesn\'t:').format(
                             j+1, args.rules), os.linesep, prettify_dict(rule)
                        ])
                    )
                if order['side'] not in ['buy', 'sell']:
                        raise RuntimeError(''.join([
                            ('An order\'s "side" must be one of {{"buy", '
                             '"sell"}}, which order #{} in this rule '
                             'from the file "{}" doesn\'t satisfy:').format(
                             j+1, args.rules), os.linesep, prettify_dict(rule)
                        ])
                    )
                if 'product_id' not in order:
                    raise RuntimeError(''.join([
                            ('An order must have a "product_id", but in the '
                             'file "{}", order #{} from this rule '
                             'doesn\'t:').format(args.rules, j+1),
                            os.linesep, prettify_dict(rule)
                        ]))
                if new_rules[i]['orders'][j]['type'] == 'limit':
                    for item in ['price', 'size']:
                        if item not in order:
                            raise RuntimeError(''.join([
                                ('If an order\'s "type" is "limit", the order '
                                 'must specify a "{}", but in the file "{}",'
                                 'order #{} from this rule doesn\'t:').format(
                                 item, args.rules, j+1),
                                 os.linesep, prettify_dict(rule)
                            ]))
                elif new_rules[i]['orders'][j]['type'] in ['market', 'stop']:
                    if 'size' not in order and 'funds' not in order:
                        raise RuntimeError(''.join([
                                ('If an order\'s "type" is "{}", the order '
                                 'must have at least one of {{"size", '
                                 '"funds"}}, but in file "{}", order #{} '
                                 'of this rule doesn\'t:').format(
                                        new_rules[i]['orders'][j]['type'],
                                        args.rules, j+1
                                    ), os.linesep, prettify_dict(rule)]))
                for stack in ['size', 'funds', 'price']:
                    try:
                        eval(order[stack].format(
                            tweet=('"The rain in Spain stays mainly '
                                   'in the plain."'),
                            available={
                                'ETH' : .01,
                                'USD' : .01,
                                'LTC' : .01,
                                'BTC' : .01
                            }, inside_bid=200, inside_ask=200))
                    except KeyError:
                        pass
                    except Exception as e:
                        raise RuntimeError(''.join([
                                ('"{}" from order #{} in the following '
                                 'rule from the file "{}" could not be '
                                 'evaluated; check the format '
                                 'and try again:').format(
                                        stack, j+1, args.rules
                                    ), os.linesep, prettify_dict(rule)]))
        rules = new_rules
        # Use _last_ entry in config file with profile name
        key = None
        try:
            with open(os.path.join(key_dir, 'config'), 'rU') as config_stream:
                line = config_stream.readline().rstrip('\n')
                while line:
                    profile_name = line[1:-1]
                    if profile_name == args.profile:
                        salt = base64.b64decode(
                                config_stream.readline().rstrip(
                                        '\n').partition(': ')[2]
                            )
                        if key is None:
                            key = KDF.PBKDF2(getpass.getpass(
                                    'Enter password for profile "{}": '.format(
                                                                profile_name
                                                            )
                                ), salt,
                                dkLen=32, count=_key_derivation_iterations
                            )
                        keys_and_secrets = []
                        for _ in range(7):
                            item, _, encoded = config_stream.readline().rstrip(
                                                    '\n').partition(': ')
                            if 'key' in item:
                                # Not actually encoded; remove leading space
                                keys_and_secrets.append(encoded)
                                continue
                            encoded = base64.b64decode(encoded)
                            cipher = AES.new(
                                    key, AES.MODE_CFB,
                                    encoded[:AES.block_size]
                                )
                            keys_and_secrets.append(
                                    cipher.decrypt(
                                            encoded
                                        )[AES.block_size:]
                                )
                    else:
                        # Skip profile
                        for _ in range(8): config_stream.readline()
                    line = config_stream.readline().rstrip('\n')
        except IOError as e:
            e.message = (
                    'Cannot find vickitrix config file. Use '
                    '"vickitrix configure" to configure vickitrix '
                    'before trading.'
                )
            raise

        # Get all twitter handles to monitor
        handles, keywords = set(), set()
        for rule in rules:
            handles.update(rule['handles'])
            keywords.update(rule['keywords'])

        try:
            # Instantiate GDAX and Twitter clients
            gdax_client = gdax.AuthenticatedClient(*keys_and_secrets[:3])
            twitter_client = Twython(*keys_and_secrets[3:7])

            # Are they working?
            get_balance(gdax_client, status_update=True)
            state = State('state.dat')
            trader = TradingStateMachine(rules, gdax_client, twitter_client,
                                         handles, state, sleep_time=args.sleep)

        except Exception:
            from traceback import format_exc
            log.error(format_exc())
            log.error(''.join(
                    [os.linesep,
                     'Chances are, this opaque error happened because either ',
                      os.linesep,
                      'a) You entered incorrect security credentials '
                      'when you were configuring vickitrix.',
                      os.linesep,
                      'b) You entered the wrong password above.']
                ))
            exit(1)

        log.info('Twitter/GDAX credentials verified.')

        while True:
            log.info('Waiting for trades; hit CTRL+C to quit...')
            trader.run()
            log.info('Rate limit error. Restarting in %d s...' % args.interval)
            time.sleep(args.interval)
