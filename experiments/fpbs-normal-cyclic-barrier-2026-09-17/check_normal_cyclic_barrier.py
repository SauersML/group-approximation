#!/usr/bin/env python3
"""Checks for fpbs-cs-barrier-hypothesis-fails-normal-cyclic.

Groups with an infinite cyclic normal subgroup Z = <z>:
  G1 = F_2 x Z                 (z central)
  G2 = Z x|_chi F_2, chi(a)=-1 (a inverts z, b centralises z; z not central)
  G3 = F_2 x D_inf, z = translation of D_inf (index-2 normal, not central)
Calibration: F_2 itself with the cyclic subgroup <a> (not normal).

(1) Core lemma: if g1 = z^m t and g2 = z^n t are distinct, then
    g1 g2 = g2 g1 (t centralises z) or g1 g1 = g2 g2 (t inverts z).
    So the core B' of a roughly branching set meets each coset <z> t at most
    once.  Checked exhaustively on windows.
(2) Calibration: in F_2 the set {a^m b : |m| <= M} is 0-roughly branching
    (products of length <= 3 are injective), and it meets the 1-tube of <a>
    in 2M+1 points.  So the cap is special to normal cyclic subgroups.
(3) Theorem 2.9 witness: A = {z^j : |j| <= L} u z^L B(R) u z^-L B(R).
    Every a = z^j has a h a^-1 in A A^-1 for all |h| <= R, so every "good"
    point lies in the two translated balls, fewer than #A/2.
    Checked by brute force for two generating sets per group.
"""
import itertools
import random


def fmul(u, v):
    u = list(u)
    for x in v:
        if u and u[-1] == -x:
            u.pop()
        else:
            u.append(x)
    return tuple(u)


def finv(u):
    return tuple(-x for x in reversed(u))


def asum(w):
    return sum(1 for x in w if abs(x) == 1)


# --- G = Z x|_chi F_2 : elements (m, w); (m,w)(m',w') = (m + chi(w) m', ww')
def make_semidirect(chi_a, chi_b):
    def chi(w):
        s = 1
        for x in w:
            s *= chi_a if abs(x) == 1 else chi_b
        return s

    def mul(g, h):
        return (g[0] + chi(g[1]) * h[0], fmul(g[1], h[1]))

    def inv(g):
        wi = finv(g[1])
        return (-chi(wi) * g[0], wi)

    e = (0, ())
    z = (1, ())
    fa = (0, (1,))
    fb = (0, (2,))
    return mul, inv, e, z, fa, fb


# --- G3 = F_2 x D_inf : elements (w, n, s); D_inf part (n,s)(n',s') = (n + (-1)^s n', s+s')
def make_f2_dinf():
    def mul(g, h):
        return (fmul(g[0], h[0]), g[1] + (-1) ** g[2] * h[1], (g[2] + h[2]) % 2)

    def inv(g):
        return (finv(g[0]), -((-1) ** g[2]) * g[1], g[2])

    e = ((), 0, 0)
    z = ((), 1, 0)
    r = ((), 0, 1)
    fa = ((1,), 0, 0)
    fb = ((2,), 0, 0)
    return mul, inv, e, z, fa, fb, r


def power(mul, inv, e, g, n):
    x = e
    base = g if n >= 0 else inv(g)
    for _ in range(abs(n)):
        x = mul(x, base)
    return x


def ball(mul, inv, e, gens, R):
    S = set(gens) | {inv(s) for s in gens}
    seen = {e}
    frontier = [e]
    for _ in range(R):
        nxt = []
        for g in frontier:
            for s in S:
                h = mul(g, s)
                if h not in seen:
                    seen.add(h)
                    nxt.append(h)
        frontier = nxt
    return seen


def core_lemma(name, mul, inv, e, z, gens, rho, M):
    T = ball(mul, inv, e, gens, rho)
    checked = 0
    for t in T:
        coset = [mul(power(mul, inv, e, z, m), t) for m in range(-M, M + 1)]
        for g1, g2 in itertools.combinations(coset, 2):
            ok = mul(g1, g2) == mul(g2, g1) or mul(g1, g1) == mul(g2, g2)
            assert ok, (name, g1, g2)
            checked += 1
    print(f"[core] {name}: rho={rho}, window |m|<={M}: {checked} coset pairs, "
          f"every pair collides at k=2 -> #(B' cap <z>t) <= 1")


def injective_upto(mul, e, Bp, kmax):
    for k in range(1, kmax + 1):
        seen = {}
        for seq in itertools.product(Bp, repeat=k):
            x = e
            for g in seq:
                x = mul(x, g)
            if x in seen and seen[x] != seq:
                return False, k
            seen[x] = seq
    return True, kmax


def calibration_f2(M):
    Bp = [fmul((1,) * m if m >= 0 else (-1,) * (-m), (2,)) for m in range(-M, M + 1)]
    ok, k = injective_upto(fmul, (), Bp, 3)
    assert ok
    print(f"[calib] F_2: {{a^m b : |m|<={M}}} injective for k<=3, meets 1-tube of <a> "
          f"in {len(Bp)} points (no cap without normality)")
    # the same shape in F_2 x Z collides immediately
    mul, inv, e, z, fa, fb = make_semidirect(1, 1)
    Bz = [mul(power(mul, inv, e, z, m), fb) for m in range(-M, M + 1)]
    ok2, k2 = injective_upto(mul, e, Bz, 2)
    assert not ok2
    print(f"[calib] F_2 x Z: {{z^m b : |m|<={M}}} collides at k={k2}")


def thm29_witness(name, mul, inv, e, z, gens, R, L):
    BR = ball(mul, inv, e, gens, R)
    zL = power(mul, inv, e, z, L)
    zmL = power(mul, inv, e, z, -L)
    line = [power(mul, inv, e, z, j) for j in range(-L, L + 1)]
    A = set(line) | {mul(zL, h) for h in BR} | {mul(zmL, h) for h in BR}
    AAi = {mul(x, inv(y)) for x in A for y in A}
    good = [a for a in A if any(mul(mul(a, h), inv(a)) not in AAi for h in BR)]
    line_good = [a for a in line if a in good]
    assert not line_good, (name, line_good[:3])
    assert 2 * len(good) < len(A), (name, len(good), len(A))
    print(f"[thm2.9] {name}: R={R}, L={L}, #B(R)={len(BR)}, #A={len(A)}, "
          f"#good={len(good)} < #A/2; line points good: 0")


def main():
    random.seed(0)
    mul1, inv1, e1, z1, a1, b1 = make_semidirect(1, 1)
    mul2, inv2, e2, z2, a2, b2 = make_semidirect(-1, 1)
    mul3, inv3, e3, z3, a3, b3, r3 = make_f2_dinf()
    groups = [
        ("F2xZ std", mul1, inv1, e1, z1, [a1, b1, z1]),
        ("F2xZ skew", mul1, inv1, e1, z1, [mul1(a1, z1), b1, mul1(z1, b1)]),
        ("Z|x F2 (a inverts z) std", mul2, inv2, e2, z2, [a2, b2, z2]),
        ("Z|x F2 (a inverts z) skew", mul2, inv2, e2, z2, [mul2(a2, z2), b2, mul2(z2, b2)]),
        ("F2xDinf std", mul3, inv3, e3, z3, [a3, b3, r3, mul3(r3, z3)]),
        ("F2xDinf skew", mul3, inv3, e3, z3, [mul3(a3, r3), mul3(b3, z3), r3, mul3(r3, z3)]),
    ]
    gensets = {"F2xZ": (a1, b1, z1), "Z|x": (a2, b2, z2), "F2xDinf": (a3, b3, z3, r3)}
    for name, mul, inv, e, z, gens in groups:
        key = [k for k in gensets if name.startswith(k)][0]
        B4 = ball(mul, inv, e, gens, 4)
        assert all(x in B4 for x in gensets[key]), ("not generating", name)
    for name, mul, inv, e, z, gens in groups:
        core_lemma(name, mul, inv, e, z, gens, rho=2, M=6)
    calibration_f2(M=3)
    for name, mul, inv, e, z, gens in groups:
        for R in (1, 2):
            nB = len(ball(mul, inv, e, gens, R))
            L = nB + 1  # 2L+1 > 2 #B(R)
            thm29_witness(name, mul, inv, e, z, gens, R, L)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
