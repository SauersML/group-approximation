#!/usr/bin/env python3
"""Checks for dkkms-seed-rigidity-fails-on-homogeneous-kernel-mixtures.

The node exhibits, on DKKMS 2-to-1 instances whose 3LIN input carries a
homogeneous kernel labelled by F_2^(m+1) (the "J-part"), a labelling of value
about 0.711 whose satisfied seed (B-)labels disagree with the honest encoding
of EVERY outer labelling on mass about 0.289 > gamma = value - 1/2.

The labelling (x a good assignment, z a homogeneous solution, y = x + z,
phi = (phi_1..phi_m) further homogeneous solutions, m = l):

    A-class C   : x|_R  if phi is injective on R_C, else y|_R
    B (V, L')   : x|_L' if phi is injective on L',  else y|_L'

Part A  exact finite-parameter formulas b, c (fractions).
Part B  brute force of one clean k-tuple (U, V) for small k, l, including a
        smoothed V, against every reference functional on X_V.
Part C  limit (l, k -> infinity) rank-chain model: search over all
        rank-threshold branch assignments with 2..4 branches.
Part D  the J-instance: regularity, homogeneity of Phi, and Monte Carlo of
        the surjectivity event on random smoothed k-tuples.

Run: python3 check_seed_mixture.py      (a few seconds; exits 0 on success)
"""
from fractions import Fraction as Fr
from itertools import product, combinations
import random
import sys

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


# ---------------------------------------------------------------- GF(2) utils
def span(vecs):
    s = {0}
    for v in vecs:
        s |= {w ^ v for w in s}
    return s


def rank(vecs):
    basis = []  # (pivot bit, vector) echelon
    for v in vecs:
        for p, b in basis:
            if v >> p & 1:
                v ^= b
        if v:
            p = v.bit_length() - 1
            basis.append((p, v))
    return len(basis)


def subspaces(ambient_basis, dim):
    """All dim-dimensional subspaces of span(ambient_basis), as frozensets."""
    seen = set()
    out = []
    amb = sorted(span(ambient_basis) - {0})
    for combo in combinations(amb, dim):
        if rank(combo) < dim:
            continue
        s = frozenset(span(combo))
        if s not in seen:
            seen.add(s)
            out.append((s, combo))
    return out


# ------------------------------------------------------------ Part A formulas
def b_exact(l, m, dprime):
    """Pr[phi injective on M], M uniform (l-1)-space of F_2^d', phi onto F_2^m."""
    r = Fr(1)
    for i in range(l - 1):
        r *= Fr(1) - Fr(2) ** (i - m)
        r /= Fr(1) - Fr(2) ** (i - dprime)
    return r


def c_exact(l, m, k):
    """Pr[phi(v) in phi(L') | phi inj on L'], v uniform on X_U minus L'+H_U."""
    num = Fr(2) ** (l - 1 + 3 * k - m) - Fr(2) ** (l - 1 + k)
    den = Fr(2) ** (3 * k) - Fr(2) ** (l - 1 + k)
    return num / den


def P(s, terms=200):
    r = 1.0
    for j in range(s + 1, s + 1 + terms):
        r *= 1 - 2.0 ** (-j)
    return r


print("Part A: limits (m = l):")
bl, cl = P(1), 0.5
px, py = bl * (1 - cl), 1 - bl
val = px + py
print(f"  b -> P_1 = {bl:.6f}, c -> 1/2, p_x -> {px:.6f}, p_y -> {py:.6f}")
print(f"  value -> {val:.6f}, gamma -> {val - 0.5:.6f}, "
      f"min branch -> {min(px, py):.6f}")
check(abs(px - P(0)) < 1e-12, "p_x limit equals P_0")
check(abs(min(px, py) - (val - 0.5) - (P(1) - 0.5)) < 1e-12,
      "limit margin over gamma equals P_1 - 1/2")
check(P(1) - 0.5 > 0.0775, "P_1 - 1/2 > 0.0775")
check(min(px, py) - (val - 0.5) / 2 > 0.183, "limit margin over gamma/2")

print("  finite l (k, d' -> infinity), bound D - gamma >= "
      "min(p_x,p_y) - (1 - bc - 1/2) - 3*2^(1-l):")
first_good = None
for l in range(3, 21):
    b = 1.0
    for i in range(l - 1):
        b *= 1 - 2.0 ** (i - l)
    px, py = b * 0.5, 1 - b
    marg = min(px, py) - (1 - b * 0.5 - 0.5) - 3 * 2.0 ** (1 - l)
    marg2 = min(px, py) - (1 - b * 0.5 - 0.5) / 2 - 3 * 2.0 ** (1 - l)
    if marg > 0 and first_good is None:
        first_good = l
    print(f"   l={l:2d} b={b:.5f} p_x={px:.5f} p_y={py:.5f} "
          f"margin(gamma)={marg:+.5f} margin(gamma/2)={marg2:+.5f}")
print(f"  first l with positive gamma-margin: {first_good}")
check(first_good is not None and first_good <= 7, "gamma-margin positive by l=7")


# ---------------------------------------------------------- Part B brute force
def parity(v):
    return bin(v).count("1") & 1


def brute(k, l, m, labels, vvars):
    """One clean tuple U of k J-blocks (variables 3i, 3i+1, 3i+2 labelled
    u, u', u+u'), all right-hand sides 0, so x = 0 is a satisfying
    assignment and z = last coordinate of Phi is a homogeneous solution.
    vvars: the variables of V (a full block = kept equation)."""
    n = 3 * k
    lab = []
    for i in range(k):
        u, w = labels[i]
        lab += [u, w, u ^ w]
    Phi = [0] * (1 << n)
    for v in range(1, 1 << n):
        low = v & -v
        Phi[v] = Phi[v ^ low] ^ lab[low.bit_length() - 1]
    xe = [7 << (3 * i) for i in range(k)]
    for e in xe:
        check(Phi[e] == 0, "Phi vanishes on x_e")
    HU = span(xe)
    kept = [xe[i] for i in range(k) if all(3 * i + j in vvars for j in range(3))]
    Hp = span(kept)
    XVbasis = [1 << t for t in vvars]
    XV = span(XVbasis)
    dprime = len(vvars) - len(kept)
    mask = (1 << m) - 1

    def phi(v):
        return Phi[v] & mask

    def z(v):
        return Phi[v] >> m & 1

    # hypotheses: phi-bar onto F_2^m and z-bar nonzero on X_V / H'
    check(rank([phi(1 << t) for t in vvars]) == m, "phi-bar surjective")
    check(any(z(1 << t) for t in vvars), "z-bar nonzero")
    Lps = [(s, bas) for s, bas in subspaces(XVbasis, l - 1)
           if len(s & HU) == 1]
    refs = [w for w in range(1 << n) if w & ~sum(XVbasis) == 0]
    nv = (1 << n) - (1 << (l - 1 + k))      # |X_U minus (L' + H_U)|
    tot = Rx = Rxy = Ry = sat = 0
    agree = {w: 0 for w in refs}
    for Lp, bas in Lps:
        LpH = span(list(bas) + xe)
        check(len(LpH) == 1 << (l - 1 + k), "dim(L'+H_U) = l-1+k")
        pb = [phi(b) for b in bas]
        injB = rank(pb) == l - 1
        zvan = all(z(b) == 0 for b in bas)
        cnt = {"x": 0, "xy": 0, "y": 0}
        for v in range(1 << n):
            if v in LpH:
                continue
            injA = rank(pb + [phi(v)]) == l
            check(not (injA and not injB), "A-injective implies B-injective")
            cnt["x" if (injA and injB) else "xy" if injB else "y"] += 1
        check(sum(cnt.values()) == nv, "direction count")
        tot += nv
        Rx += cnt["x"]
        Rxy += cnt["xy"]
        Ry += cnt["y"]
        s_here = cnt["x"] + cnt["y"] + (cnt["xy"] if zvan else 0)
        sat += s_here
        # B-label on the basis of L': 0 (= x) in x-region, z(b) in y-region
        blab = [0 if injB else z(b) for b in bas]
        for w in refs:
            if all(parity(w & b) == t for b, t in zip(bas, blab)):
                agree[w] += s_here
    tot = Fr(tot)
    Rx, Rxy, Ry, sat = (Fr(t) / tot for t in (Rx, Rxy, Ry, sat))
    agree = {w: Fr(a) / tot for w, a in agree.items()}
    b = b_exact(l, m, dprime)
    c = c_exact(l, m, k)
    check(Rx == b * (1 - c), f"R_x formula k={k} l={l}")
    check(Rxy == b * c, f"R_xy formula k={k} l={l}")
    check(Ry == 1 - b, f"R_y formula k={k} l={l}")
    best = max(agree.values())
    D = sat - best
    lower = min(Rx, Ry) - Fr(2) ** (2 - l)
    check(D >= lower, "dishonest mass >= min branch - 2^(2-l)")
    check(sat <= 1 - b * c + Fr(2) ** (1 - l), "value <= 1 - bc + 2^(1-l)")
    print(f"  k={k} l={l} m={m} d'={dprime}: val={float(sat):.5f} "
          f"R_x={float(Rx):.5f} R_xy={float(Rxy):.5f} R_y={float(Ry):.5f} "
          f"best ref agreement={float(best):.5f} dishonest={float(D):.5f} "
          f"(formulas exact: b={b}, c={c})")
    return sat, D


print("Part B: brute force of one clean tuple, all references on X_V")
brute(2, 2, 2, [(1, 2), (4, 3)], list(range(6)))
brute(2, 3, 3, [(1, 2), (4, 8)], list(range(6)))
brute(2, 3, 3, [(1, 2), (4 ^ 8, 8)], [0, 1, 2, 3])      # block 2 smoothed
brute(3, 2, 2, [(1, 2), (4, 1), (2, 4)], list(range(9)))
brute(3, 2, 2, [(1, 2), (4, 1), (2, 4)], [0, 1, 2, 3, 4, 5, 6])  # smoothed


# ------------------------------------------------- Part C rank-chain search
def rank_chain(l, m):
    """Joint law of (rank phi(L'), rank phi(L)) as n, k -> infinity:
    phi(L') = span of l-1 iid uniform vectors of F_2^m, one more for L."""
    dist = {0: 1.0}
    for _ in range(l - 1):
        new = {}
        for r, p in dist.items():
            up = 1 - 2.0 ** (r - m)
            new[r + 1] = new.get(r + 1, 0) + p * up
            new[r] = new.get(r, 0) + p * (1 - up)
        dist = new
    joint = {}
    for r, p in dist.items():
        up = 1 - 2.0 ** (r - m)
        joint[(r, r + 1)] = joint.get((r, r + 1), 0) + p * up
        joint[(r, r)] = joint.get((r, r), 0) + p * (1 - up)
    return {key: p for key, p in joint.items() if p > 1e-13}


def search(l, m, K):
    joint = rank_chain(l, m)
    rB = sorted({a for a, _ in joint})
    rA = sorted({b for _, b in joint})
    best = {"gap": (-9, None), "gap2": (-9, None), "vg": (0, 0), "vg2": (0, 0)}
    caps = {t: (0.0, None) for t in (0.45, 0.4, 0.35, 0.3, 0.25)}
    for fb in product(range(K), repeat=len(rB)):
        if fb[0] != 0:          # symmetry: first B-rank gets branch 0
            continue
        mb = dict(zip(rB, fb))
        for fa in product(range(K), repeat=len(rA)):
            ma = dict(zip(rA, fa))
            mass = [0.0] * K
            for (a, b), p in joint.items():
                if mb[a] == ma[b]:
                    mass[mb[a]] += p
            val = sum(mass)
            D = val - max(mass)
            g = val - 0.5
            if D > g > 0 and val > best["vg"][0]:
                best["vg"] = (val, max(mass))
            if D > g / 2 and g > 0 and val > best["vg2"][0]:
                best["vg2"] = (val, max(mass))
            if g > 0 and D - g > best["gap"][0]:
                best["gap"] = (D - g, (val, max(mass), fb, fa))
            if g > 0 and D - g / 2 > best["gap2"][0]:
                best["gap2"] = (D - g / 2, (val, max(mass), fb, fa))
            for t in caps:
                if max(mass) <= t and val > caps[t][0]:
                    caps[t] = (val, (mass, fb, fa))
    return rB, rA, best, caps


print("Part C: rank-threshold labellings, l = 30 (limit model)")
overall = -1
vmax = vmax2 = 0
for s in range(-2, 4):
    m = 30 + s
    for K in (2, 3):
        rB, rA, best, caps = search(30, m, K)
        g, info = best["gap"]
        overall = max(overall, g)
        capstr = " ".join(f"{t}:{v:.3f}" for t, (v, _) in caps.items())
        print(f"  m=l{s:+d} K={K}: max(D - gamma)={g:+.5f} at val={info[0]:.4f}"
              f" maxbranch={info[1]:.4f}; max(D - gamma/2)="
              f"{best['gap2'][0]:+.5f}; max val with D>gamma {best['vg'][0]:.4f},"
              f" with D>gamma/2 {best['vg2'][0]:.4f}; best value with max branch <= t: {capstr}")
        vmax = max(vmax, best["vg"][0])
        vmax2 = max(vmax2, best["vg2"][0])
check(overall > 0.0775, "rank search reproduces the m = l example")
print(f"  largest value with D > gamma: {vmax:.4f}; with D > gamma/2: {vmax2:.4f}")


# ---------------------------------------------------------------- Part D
print("Part D: the J-instance (m = 3, labels in F_2^4 \\ 0)")
MJ = 3
pts = list(range(1, 2 ** (MJ + 1)))
lines = sorted({tuple(sorted((u, w, u ^ w))) for u in pts for w in pts
                if u != w})
deg = {u: sum(u in e for e in lines) for u in pts}
check(len(set(deg.values())) == 1, "J is regular")
check(all((a ^ b ^ c) == 0 for a, b, c in lines),
      "Phi(var) = label is a homogeneous solution")
print(f"  {len(pts)} variables, {len(lines)} equations, every variable in "
      f"{deg[1]} equations; Phi vanishes on every equation vector")
NCOP, KJ, BETA, TRIALS = 60, 8, 0.3, 4000
rng = random.Random(20260917)


def span_rank(labels):
    basis = []
    for v in labels:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)


fails = 0
for _ in range(TRIALS):
    used, tup = set(), []
    while len(tup) < KJ:
        cop, e = rng.randrange(NCOP), rng.choice(lines)
        if any((cop, u) in used for u in e):
            continue
        used |= {(cop, u) for u in e}
        tup.append(e)
    vlabels = []
    for e in tup:
        if rng.random() < 1 - BETA:
            vlabels += list(e)
        else:
            vlabels.append(rng.choice(e))
    # Phi on X_V / H' has image span(labels of the variables of V)
    if span_rank(vlabels) < MJ + 1:
        fails += 1
bound = (2 ** (MJ + 1)) * 2.0 ** (-KJ)
print(f"  k = {KJ}, beta = {BETA}: surjectivity of Phi on X_V/H' fails with "
      f"frequency {fails / TRIALS:.4f}; bound 2^(m+1) 2^(-t) = {bound:.4f}")
check(fails / TRIALS <= bound + 0.01, "surjectivity failure below bound")

print()
if FAIL:
    print(f"{len(FAIL)} CHECK(S) FAILED")
    sys.exit(1)
print("ALL CHECKS PASSED")
sys.exit(0)
