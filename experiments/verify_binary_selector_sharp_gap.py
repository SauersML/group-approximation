"""Exact equality examples for the standalone binary selector rank bounds.

This verifies two finite examples; the all-dimensional theorem has a prose proof.
It does not verify a group-level non-MF construction.
"""

from fractions import Fraction as F

def targets(m, positive):
    gauge = [1] * positive + [-1] * (m - positive)
    label1 = [-1] * 2 + [1] * 6
    label2 = [-1] + [1] * 7
    return [[a * b for a in label for b in gauge]
            for label in (label1, label2)]

def source(target, negative_rank):
    negative = [i for i, x in enumerate(target) if x == -1]
    positive = [i for i, x in enumerate(target) if x == 1]
    if negative_rank <= len(negative):
        chosen = negative[:negative_rank]
    else:
        chosen = negative + positive[:negative_rank - len(negative)]
    chosen = set(chosen)
    return [-1 if i in chosen else 1 for i in range(len(target))]

def audit(m, positive):
    t1, t2 = targets(m, positive)
    d = 8 * m
    r1, r2 = source(t1, d // 2), source(t2, d // 4)
    energy = [F(sum((a-b)**2 for a, b in zip(r, t)), d)
              for r, t in ((r1, t1), (r2, t2))]
    opnorm = [max(abs(a-b) for a, b in zip(r, t))
              for r, t in ((r1, t1), (r2, t2))]
    ranks = [sum(x == -1 for x in t) for t in (t1, t2)]
    return d, ranks, energy, opnorm

assert audit(6, 5) == (48, [16, 12], [F(2, 3), F(0)], [2, 0])
assert audit(10, 7) == (80, [32, 28], [F(2, 5), F(2, 5)], [2, 2])

# Binary atomic bound: s_i=1, t_i=2/3.
inverse = abs(F(2, 3) - 1)
complete = abs(2 * F(2, 3) - 1)
assert inverse == complete == F(1, 3)
assert 2 * inverse + complete == 1

print(audit(6, 5))
print(audit(10, 7))
print('All exact arithmetic checks passed.')
