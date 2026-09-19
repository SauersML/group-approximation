#!/usr/bin/env python3
"""cmp28.py S26dump S28dump: check S_26 is contained in S_28 and give the length histogram of
the states of S_28 outside S_26, with the first few examples of each length <= 24."""
import sys
from collections import Counter
s26 = set(open(sys.argv[1]).read().split('\n')) - {''}
n = inc = 0; new = Counter(); ex = {}
for l in open(sys.argv[2]):
    l = l.rstrip('\n'); n += 1
    if l in s26: inc += 1; continue
    L = len(l) - 1; new[L] += 1
    if L <= 24 and len(ex.setdefault(L, [])) < 3: ex[L].append(l)
print('S_28 states %d; contains all %d of the %d S_26 states: %s' % (n, inc, len(s26), inc == len(s26)))
print('S_28 minus S_26 by length:', sorted(new.items()))
for L in sorted(ex): print('  length %d examples: %s' % (L, ' | '.join(ex[L])))
