"""Checks for the lamplighter automaton a = sigma(a,b), b = (a,b) (binary alphabet).

With c = b^-1 a and d_k = b^k c b^-k:
  1. c^2 and [c, d_k] (k = 1..K) lie in K_infinity (die after finitely many free splittings);
  2. psi(c) = sigma(c, c^-1) at word level;
  3. b^m|_1 = b^m for all m (so G is not contracting);
  4. sanity: short words in b, c that are nontrivial in Z/2 wr Z act nontrivially.
Run: python3 lamp.py [K]
"""
import sys
sys.path.insert(0, '.')
from autom import Automaton

A = Automaton(2, {'a': ((1, 0), ('a', 'b')), 'b': ((0, 1), ('a', 'b'))})
a, b = A.idx['a'], A.idx['b']
c = (-b, a)
inv = lambda w: tuple(-u for u in reversed(w))
bk = lambda k: (b,) * k if k >= 0 else (-b,) * (-k)
d = lambda k: bk(k) + c + bk(-k)
comm = lambda x, y: x + y + inv(x) + inv(y)

K = int(sys.argv[1]) if len(sys.argv) > 1 else 10
print('psi(c):', A.root_perm(c), [A.fmt(s) for s in A.sections(c)])
print('c^2 in K_inf:', A.in_K_inf(c + c))
for k in range(1, K + 1):
    w = comm(c, d(k))
    print(f'[c, d_{k}] len {len(A.reduce(w))}: in K_inf {A.in_K_inf(w)}, reachable {len(A.reach(w))}')
print('b^m|_1 == b^m for m=1..20:', all(A.sections(bk(m))[1] == bk(m) for m in range(1, 21)))

# 4. elements b^m * prod_{j in S} d_j with (m, S) != (0, {}) should be nontrivial
import itertools
ok = True
for m in range(-3, 4):
    for r in range(0, 4):
        for S in itertools.combinations(range(-3, 4), r):
            if m == 0 and not S:
                continue
            w = bk(m)
            for j in S:
                w = w + d(j)
            if A.is_trivial(w):
                ok = False
                print('unexpected relator', m, S)
print('normal forms b^m d_S (|m|<=3, S in [-3,3], |S|<=3) all nontrivial:', ok)
