import itertools, sys, time
sys.path.insert(0, '/private/tmp/claude-501/-Users-anson/66aa0277-2361-4106-8c7e-0106b4ddf9d5/scratchpad')
from fsm import *
from test3 import check_hist, check_prop55

# non-binary value spaces
V3vals = {'a': (0, 1, 2), 'b': (0, 1), 'c': (0, 1)}
check_hist({'a': (), 'b': ('a',), 'c': ('b',)}, V3vals, "chain, |Val_a|=3", sets=True)
check_prop55({'a': (), 'b': ('a',), 'c': ('b',)}, V3vals, "chain |Val_a|=3", maxset=2)
V3b = {'a': (0, 1), 'b': (0, 1), 'c': (0, 1, 2)}
check_hist({'a': (), 'b': (), 'c': ('a', 'b')}, V3b, "collider, |Val_c|=3", sets=True)
# v-structure where child of collider has an extra non-Z parent
G = {'a': (), 'b': (), 'c': ('a', 'b')}
check_hist(G, {'a': (0, 1, 2), 'b': (0, 1), 'c': (0, 1)}, "collider |Val_a|=3", sets=True)
