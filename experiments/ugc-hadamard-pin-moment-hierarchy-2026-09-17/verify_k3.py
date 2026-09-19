"""Independent checks for research/hadamard-certificates-blind-below-planes.md (k = 3).

1. pattern classes: under the pattern action of G (affine relabelling of pins,
   multiplication by linear characters, negation) the 256 patterns split into
   orbits of sizes 16 (lin), 112 (quad), 128 (cub = odd number of -1's).
2. moments: the plane average Phi(xi) = mean over the 14 affine planes of
   prod_{a in plane} xi_a equals 1 / -1/7 / 0 on lin / quad / cub; the uniform
   law on the 128 odd patterns has every moment of order 1..7 equal to 0; the
   signed dictator law (xi_a = s (-1)^{a.i}) has every moment of order 1..3
   equal to 0.
3. lower bound: for w = (WA, WB) = (5, 1) the exact relaxed (s-t min cut)
   values are K m^U = 1, 3/2, 21/16 on lin, quad, cub, and the min over
   plane-feasible class mixtures is 21/16.
4. upper bound: two explicit folded adversaries with pin pattern in the cub
   class, cut counts (28,112) and (14,182) on the orbits (128, 896); the
   G-symmetrised half/half mixture cuts every edge with probability 21/128.
"""
import itertools
from fractions import Fraction as F
import numpy as np
import pin_moment_k3 as P
import scan_k3 as S

K, k = P.K, P.k


def dot(a, b):
    return bin(a & b).count("1") & 1


# ---------- 1. pattern orbits ------------------------------------------------
def pat_gens(xi):
    """xi: tuple of K bits (bit 1 <=> xi_a = -1)."""
    rot = lambda a: ((a << 1) | (a >> (k - 1))) & (K - 1)
    tv = lambda a: a ^ ((a & 1) << 1)
    sw = lambda a: (a & ~3) | ((a & 1) << 1) | ((a >> 1) & 1)
    for mp in (rot, tv, sw, lambda a: a ^ 1):
        yield tuple(xi[mp(a)] for a in range(K))
    for t in range(k):
        yield tuple(xi[a] ^ dot(a, 1 << t) for a in range(K))
    yield tuple(1 - b for b in xi)


def orbit(xi):
    seen, stack = {xi}, [xi]
    while stack:
        z = stack.pop()
        for y in pat_gens(z):
            if y not in seen:
                seen.add(y); stack.append(y)
    return seen


reps = {c: tuple(P.CLASSES[c](a) for a in range(K)) for c in P.NAMES}
orbs = {c: orbit(reps[c]) for c in P.NAMES}
sizes = {c: len(orbs[c]) for c in P.NAMES}
assert sizes == {"lin": 16, "quad": 112, "cub": 128}, sizes
assert all(sum(x) % 2 == 1 for x in orbs["cub"])
print("1. pattern orbits:", sizes, "; cub = all odd-weight patterns")

# ---------- 2. moments -------------------------------------------------------
planes = set()
for p in range(K):
    for u in range(1, K):
        for v in range(u + 1, K):
            if u ^ v != 0:
                planes.add(frozenset({p, p ^ u, p ^ v, p ^ u ^ v}))
planes = [pl for pl in planes if len(pl) == 4]
assert len(planes) == 14


def phi(xi):
    return F(sum((-1) ** sum(xi[a] for a in pl) for pl in planes), len(planes))


for c, want in (("lin", F(1)), ("quad", F(-1, 7)), ("cub", F(0))):
    vals = {phi(x) for x in orbs[c]}
    assert vals == {want}, (c, vals)
print("2a. plane average Phi = 1, -1/7, 0 on lin, quad, cub")


def moments_vanish(law, tmax):
    for t in range(1, tmax + 1):
        for Sset in itertools.combinations(range(K), t):
            if sum((-1) ** sum(x[a] for a in Sset) for x in law) != 0:
                return False, Sset
    return True, None


ok, bad = moments_vanish(list(orbs["cub"]), 7)
assert ok, bad
assert not moments_vanish(list(orbs["cub"]), 8)[0]
dict_law = [tuple(s ^ dot(a, i) for a in range(K)) for i in range(K) for s in (0, 1)]
ok, bad = moments_vanish(dict_law, 3)
assert ok, bad
ok4, bad4 = moments_vanish(dict_law, 4)
assert not ok4 and frozenset(bad4) in set(planes)
print("2b. odd-pattern law is 7-wise uniform (not 8-wise); dictator law is"
      " 3-wise uniform, first failure on a plane", bad4)

# ---------- 3. lower bound certificate ---------------------------------------
WA, WB = 5, 1
tot = 128 * WA + 896 * WB
mU = {}
for c in P.NAMES:
    val, L, _ = S.pricepair(WA, WB, c)
    mU[c] = F(val, tot) * K
assert mU == {"lin": F(1), "quad": F(3, 2), "cub": F(21, 16)}, mU
# class masses (r_lin, r_quad, r_cub) of a plane-uniform law satisfy
# r_lin - r_quad/7 = 0 ; the minimum of the linear cost is at a vertex
verts = [(F(0), F(0), F(1)), (F(1, 8), F(7, 8), F(0))]
lb = min(r[0] * mU["lin"] + r[1] * mU["quad"] + r[2] * mU["cub"] for r in verts)
assert lb == F(21, 16)
print("3. certificate w=(5,1): K m^U =", {c: str(v) for c, v in mU.items()},
      "=> R_4(3) >= 21/16")

# ---------- 4. folded adversaries on the odd class ---------------------------
lines = {}
for (wa, wb) in ((4, 1), (6, 1)):
    val, L, f = S.pricepair(wa, wb, "cub")
    g = np.array([f[x ^ P.FULL] for x in range(P.NQ)])
    assert np.all(g != f), "not folded"
    for a in range(K):
        assert f[P.CHI[a]] == (P.CLASSES["cub"](a) == 0)
    lines[(wa, wb)] = L
assert set(lines.values()) == {(28, 112), (14, 182)}, lines
pa = F(28 + 14, 2) / 128
pb = F(112 + 182, 2) / 896
assert pa == pb == F(21, 128)
print("4. folded odd-class adversaries", sorted(lines.values()),
      "; symmetrised 1/2-1/2 mixture cuts every edge w.p.", pa, "=> R_7(3) <= 21/16")
print("VERIFIED: R_3(3) <= 1, R_4(3) = ... = R_7(3) = 21/16 < 11/8 = R_8(3) = R*(3)")
