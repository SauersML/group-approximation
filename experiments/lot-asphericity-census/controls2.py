#!/usr/bin/env python3
"""Calibration of lot2.py against Barreto--Minian (arXiv:2308.07447) examples."""
from collections import Counter
from lot2 import *
from lot import rel, cyclomatic

ok = []
def expect(cond, msg):
    ok.append(bool(cond)); print(('PASS ' if cond else 'FAIL ') + msg, flush=True)

def word(s, names):
    """Parse 'a- c- b a' into letters."""
    out = []
    for tok in s.split():
        out.append((names.index(tok[0]), -1 if tok.endswith('-') else 1))
    return out

N = 'abcd'
# Def. 2.2 example: r = a^-1 b^-1 c b^-1 a b, totals -1,-2,-1,-2,-1,0, m(r) = {b, c, b, a}.
r = word('a- b- c b- a b', N)
expect(minima(r) == Counter({1: 2, 2: 1, 0: 1}), 'D2.2 m(r) = {b,c,b,a}')

# Example 2.8: m(r1) = {a,b}, m(r2) = {d,b}; Theorem 2.5 applies.
r1 = word('a- c- b- a- b a d c b- d', N)
r2 = word('c- a- b- d- b a d c b- d', N)
r3 = word('a- b- c- a c d b- c- a d', N)
expect(minima(r1) == Counter({0: 1, 1: 1}), 'E2.8 m(r1) = {a,b}')
expect(minima(r2) == Counter({3: 1, 1: 1}), 'E2.8 m(r2) = {d,b}')
expect(test_bm25(4, [r1, r2, r3]) is not None, 'E2.8 Theorem 2.5 test passes')

# Example 2.19: m(r1) = {c,a,c,a}, m(r2) = {b,c,b,c}; weakly concatenable, order r2, r1.
s1 = word('a- c- a a a b- b- c- a b', N)
s2 = word('c- b- c b- c a b a- b a-', N)
expect(minima(s1) == Counter({2: 2, 0: 2}), 'E2.19 m(r1) = {c,a,c,a}')
expect(minima(s2) == Counter({1: 2, 2: 2}), 'E2.19 m(r2) = {b,c,b,c}')
expect(test_bm218(3, [s1, s2]) is not None, 'E2.19 Theorem 2.18 test passes')

# Label presentations: substitution self-check on a reduced LOT of diameter 4, and the count
# of relators equals the number of labels minus one.
E = [(0, 2, 1), (1, 3, 2), (3, 1, 2), (3, 0, 4)]
E = [(0, 3, 1), (1, 0, 2), (2, 4, 3), (3, 1, 4)]
cnt = 0
for root, g, RL in label_presentations(5, E):
    cnt += 1
    expect(len(RL) == g - 1 and all(sum(e for _, e in r) == 0 for r in RL),
           'LP root %d: %d generators, %d exponent-zero relators' % (root, g, len(RL)))
expect(cnt == len({l for (_, l, _) in E}), 'LP one presentation per label root')

# Corollary 3.1 agreement on the LOT presentation: if I or T has at most one cycle, Thm 2.5
# on the minima or maxima must also apply (Cor. 3.1 is derived from Thm 2.5).
import itertools
agree, tried = 0, 0
for labs in itertools.product(range(5), repeat=4):
    path = [(0, 1), (1, 2), (2, 3), (3, 4)]
    if any(l in p for l, p in zip(labs, path)): continue
    EE = [(u, l, v) for (u, v), l in zip(path, labs)]
    ci = cyclomatic(5, [(l, t) for (i, l, t) in EE]); ct = cyclomatic(5, [(l, i) for (i, l, t) in EE])
    if min(ci, ct) <= 1:
        tried += 1; agree += test_bm25(5, [rel(e) for e in EE]) is not None
expect(tried > 0 and agree == tried, 'Cor 3.1 cases all pass Thm 2.5 test (%d/%d)' % (agree, tried))

print('CONTROLS2', 'ALL_PASS' if all(ok) else 'SOME_FAIL', '%d/%d' % (sum(ok), len(ok)))
