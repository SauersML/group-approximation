"""Barrington lemma check for A_5, used in
research/alternating-v-full-group-wp-computes-sft-language-proof.md.

Claim checked: every 5-cycle rho in A_5 is a commutator [r1, r2] = r1 r2 r1^-1 r2^-1
of two 5-cycles r1, r2.  Exhaustive over all 24 five-cycles.
"""
from itertools import permutations

N = 5
ALL = list(permutations(range(N)))


def mul(p, q):  # (p*q)(i) = p(q(i))
    return tuple(p[q[i]] for i in range(N))


def inv(p):
    r = [0] * N
    for i, pi in enumerate(p):
        r[pi] = i
    return tuple(r)


def is_5cycle(p):
    i, k = 0, 0
    while True:
        i = p[i]
        k += 1
        if i == 0:
            return k == N


def comm(a, b):
    return mul(mul(a, b), mul(inv(a), inv(b)))


cycles = [p for p in ALL if is_5cycle(p)]
assert len(cycles) == 24
bad = []
for rho in cycles:
    if not any(comm(a, b) == rho for a in cycles for b in cycles):
        bad.append(rho)
print("five-cycles:", len(cycles), "not commutators of two five-cycles:", len(bad))
assert not bad
print("OK")
