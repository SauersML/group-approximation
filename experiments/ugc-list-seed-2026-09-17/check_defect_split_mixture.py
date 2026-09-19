#!/usr/bin/env python3
"""Checks for dkkms-list-seed-needs-lists-exponential-in-l.

Part A: exact law of the nullity N of phi-bar on a uniform (l-1)-subspace of
        Q = F_2^d (phi-bar : Q -> F_2^l surjective), for finite d and d -> oo;
        the value bound v(l) = 1 - E[2^(-1-N)], the defect-line mass P(N=1),
        and the certified list-size lower bound.
Part B: exact enumeration of the image (limit) model on F_2^(l+s) for small
        (l, s): W = span(u_1..u_(l-1)), W~ = W + <u_l>, u_i iid uniform;
        class c(S) = S meet K, K = 0 x F_2^s.  Checks
          Pr[c(W~) = c(W)] >= 1 - E[2^(-1-N)]   (growth bound),
          max_d Pr[(0,d) in W] <= 2^(-s).
Exits 0 iff every check passes.
"""
from fractions import Fraction as Fr
import itertools, sys

ok = True


def check(cond, msg):
    global ok
    print(("PASS " if cond else "FAIL ") + msg)
    ok = ok and cond


def nullity_law(l, d=None):
    """Law of N = (l-1) - rank(phi-bar on M-bar), M-bar uniform in Gr(F_2^d, l-1).
    Sequential basis: next vector uniform off span(q_1..q_i); its image stays in
    the current r-dim image span with prob (2^(d-l+r) - 2^i)/(2^d - 2^i);
    d = None is the limit d -> oo, stay prob 2^(r-l)."""
    dist = {0: Fr(1)}
    for i in range(l - 1):
        new = {}
        for r, p in dist.items():
            if d is None:
                stay = Fr(2 ** r, 2 ** l)
            else:
                stay = Fr(2 ** (d - l + r) - 2 ** i, 2 ** d - 2 ** i)
            new[r] = new.get(r, 0) + p * stay
            new[r + 1] = new.get(r + 1, 0) + p * (1 - stay)
        dist = new
    return {(l - 1) - r: p for r, p in dist.items()}


print("Part A: nullity law, value and list bound (limit k, d -> oo)")
print(" l   P(N=0)    P(N=1)    v(l)=1-E2^(-1-N)  gamma    Ddef>=     tmin(s=l)")
rows = {}
for l in [5, 6, 7, 8, 10, 12, 16, 20, 30, 40]:
    law = nullity_law(l)
    assert sum(law.values()) == 1
    EN = sum(p * Fr(1, 2 ** (1 + n)) for n, p in law.items())
    v = 1 - EN
    p1 = law.get(1, 0)
    gamma = v - Fr(1, 2)
    # satisfied defect-line mass: class 1-dim and no growth (growth prob 1/4);
    # minus 3*2^(-s-1), weaker than the proved loss (3/4)*2^(-s-1) from
    # M-bar meeting ker Phi-bar (route Step 4), s = l;
    # coverage per reference <= 2^(-s) + 2^(3-l)
    s = l
    Ddef = p1 * Fr(3, 4) - Fr(3, 2 ** (s + 1))
    per_ref = Fr(1, 2 ** s) + Fr(8, 2 ** l)
    need = Ddef - gamma / 2
    tmin = need / per_ref
    rows[l] = (v, gamma, Ddef, tmin)
    print(f"{l:2d}  {float(law[0]):.6f}  {float(p1):.6f}  {float(v):.6f}          "
          f"{float(gamma):.4f}   {float(Ddef):.5f}   {float(tmin):.1f}")
check(all(rows[l][0] > Fr(1, 2) + Fr(1, 10) for l in rows), "v(l) > 0.6 for all listed l")
check(all(rows[l][3] >= Fr(2 ** l, 64) for l in rows), "t_min >= 2^(l-6) for all listed l")
# Corollary LS range: every 8 <= l <= 64 (beyond, Lemma 6: TV(N_l, N_64) < 2^-64)
cor_ok = True
for l in range(8, 65):
    law = nullity_law(l)
    v = 1 - sum(p * Fr(1, 2 ** (1 + n)) for n, p in law.items())
    Ddef = law.get(1, 0) * Fr(3, 4) - Fr(3, 2 ** (l + 1))
    tmin = (Ddef - (v - Fr(1, 2)) / 2) / (Fr(1, 2 ** l) + Fr(8, 2 ** l))
    cor_ok = cor_ok and v >= Fr(6096, 10000) and Ddef >= Fr(28, 100) and tmin >= Fr(2 ** l, 64)
check(cor_ok, "for all 8 <= l <= 64: v(l) >= 0.6096, Ddef(l,l) >= 0.28, t_min >= 2^(l-6)")
# Lemma 6: TV(N_(l+1), N_l) <= 2^(-1-l)
for l in [5, 8, 12]:
    a, b = nullity_law(l), nullity_law(l + 1)
    tv = sum(abs(a.get(n, 0) - b.get(n, 0)) for n in set(a) | set(b)) / 2
    check(tv <= Fr(1, 2 ** (l + 1)), f"TV(N_{l+1}, N_{l}) <= 2^-{l+1}")
# b = P(N=0) matches Theorem M's b_l in the limit
for l in [5, 10]:
    bl = Fr(1)
    for j in range(2, l + 1):
        bl *= 1 - Fr(1, 2 ** j)
    check(nullity_law(l)[0] == bl, f"P(N=0) = b_l at l={l}")
# finite d converges to the limit
for l in [5, 7]:
    lim = nullity_law(l)
    fin = nullity_law(l, d=3 * l + 20)
    tv = sum(abs(lim.get(n, 0) - fin.get(n, 0)) for n in set(lim) | set(fin)) / 2
    check(tv <= Fr(2 ** l, 2 ** (3 * l + 20 - 2)), f"finite-d law within 2^(l+2-d) of limit at l={l}")

print("\nPart B: exact image model on F_2^(l+s)")


def span(vs):
    S = {0}
    for v in vs:
        S |= {x ^ v for x in S}
    return frozenset(S)


def image_check(l, s):
    m = l + s
    Kmask = (1 << s) - 1          # K = low s bits  (0 x F_2^s)
    vecs = range(1 << m)
    tot = 0
    same = 0
    bound_num = 0
    hit = {}
    for us in itertools.product(vecs, repeat=l - 1):
        W = span(us)
        # nullity of phi (high l bits) on the (l-1) generators
        phiW = span([u >> s for u in us])
        rank = len(phiW).bit_length() - 1
        N = (l - 1) - rank
        cW = frozenset(x for x in W if x & ~Kmask == 0)
        for x in cW:
            if x:
                hit[x] = hit.get(x, 0) + (1 << m)
        for u in vecs:
            tot += 1
            Wt = W | frozenset(x ^ u for x in W)
            cWt = frozenset(x for x in Wt if x & ~Kmask == 0)
            same += (cWt == cW)
        bound_num += (1 << m) * Fr(1, 2 ** (1 + N))
    pr_same = Fr(same, tot)
    bound = 1 - bound_num / tot
    mx = max(hit.values()) / Fr(tot) if hit else Fr(0)
    check(pr_same >= bound, f"(l,s)=({l},{s}) Pr[c same]={float(pr_same):.5f} >= {float(bound):.5f}")
    check(mx <= Fr(1, 2 ** s), f"(l,s)=({l},{s}) max_d Pr[(0,d) in W]={float(mx):.5f} <= 2^-s")


for l, s in [(3, 1), (3, 2), (4, 1), (3, 3)]:
    image_check(l, s)

print("\nALL PASS" if ok else "\nSOME CHECK FAILED")
sys.exit(0 if ok else 1)
