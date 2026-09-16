"""Exact checks for the Hantzsche-Wendt example in Section 7 of
research/artifacts/left-orderable-jensen-determinant-2026-09-16.md.

1. The defining relations a^-1 b^2 a = b^-2 and b^-1 a^2 b = a^-2 hold for the
   affine maps a, b (so the abelianization is killed by 4).
2. For v = (-3/17, 43/17, 0), p = (22/19, 4/19, 21/19) and S = {e, a, b}:
   no ties inside the sets gamma s^-1 S for gamma in the four coset
   representatives, and N_S(gamma^-1 omega) = 1 for each of them.
3. The distribution of min S over the orbit {gamma^-1 omega}: by (2.1),
   min_{gamma^-1 omega}(S) = gamma^-1 min_omega(gamma S).
"""
from fractions import Fraction as Fr
from hw_random_order import mul, inv, E, a, b

v = [Fr(-3, 17), Fr(43, 17), Fr(0)]
p = [Fr(22, 19), Fr(4, 19), Fr(21, 19)]
S = [E, a, b]
names = {E: "e", a: "a", b: "b"}

def Hq(g):
    A, t = g
    return sum(v[i] * (A[i] * p[i] + t[i]) for i in range(3))

def argmin(T):
    vals = [Hq(h) for h in T]
    assert len(set(vals)) == len(vals), "tie"
    return T[vals.index(min(vals))]

# 1. relations
b2 = mul(b, b); a2 = mul(a, a)
assert mul(mul(inv(a), b2), a) == inv(b2)
assert mul(mul(inv(b), a2), b) == inv(a2)
print("relations a^-1 b^2 a = b^-2 and b^-1 a^2 b = a^-2: ok")

# 2. N_S on the four coset representatives
reps = [E, a, b, mul(a, b)]
for g in reps:
    cnt = sum(1 for s in S if argmin([mul(mul(g, inv(s)), x) for x in S]) == g)
    print("N_S at representative with linear part", g[0], "=", cnt)
    assert cnt == 1

# 3. distribution of min S over the orbit points gamma^-1 omega
dist = {}
for g in reps:
    m = argmin([mul(g, x) for x in S])        # min_omega(gamma S)
    k = mul(inv(g), m)                        # min_{gamma^-1 omega}(S)
    dist[names[k]] = dist.get(names[k], 0) + 1
print("min S over the 4 orbit points (counts):", dist)
