#!/usr/bin/env python3
"""Checks for fpbs-choi-seo-set-family-hypothesis-fails-with-infinite-centre.

Choi--Seo arXiv:2508.08932, thm:hutchcroft1plus2 (CS4), asks for R > 0 such
that for every finite A, at least #A/2 points a of A admit g, h with
|g|,|h| <= R, A inside a H(g) and H(g) disjoint from h H(g).  That forces
a h a^-1 not in A A^-1 (necessary condition N).  We call a point a of A
"good" if some h in the R-ball has a h a^-1 not in A A^-1.

For a finite E put D_R(E) = { a h a^-1 : a in E, |h| <= R } and A = E u D_R(E).
Lemma: every a in E is bad, so #good <= #(D_R(E) minus E).  Whenever
#(D_R(E) minus E) < #E, fewer than half of A is good and CS4 fails at R.

This script
  (1) builds A on Cayley graphs of F_2 x Z (two generating sets) and counts good
      points by brute force, confirming #good < #A / 2;
  (2) counts D_R(E) for lamplighter sets and for F_2 x lamplighter
      (informational: compression holds at R=1 and fails at R=2, so the
      lemma does not reach products with a lamplighter factor);
  (3) calibrates on F_2 (acylindrically hyperbolic, where CS4 holds), where
      #(D_R(E) minus E) >= #E on every tested E.
"""
import itertools
import random


# ---------- free group F_2 on letters 1,2 (inverses -1,-2) ----------
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


# ---------- F_2 x Z ----------
def pmul(x, y):
    return (fmul(x[0], y[0]), x[1] + y[1])


def pinv(x):
    return (finv(x[0]), -x[1])


PE = ((), 0)


def ball(gens, mul, e, R):
    """Word-metric ball of radius R for the symmetric closure of gens."""
    seen = {e}
    frontier = [e]
    for _ in range(R):
        new = []
        for x in frontier:
            for s in gens:
                y = mul(x, s)
                if y not in seen:
                    seen.add(y)
                    new.append(y)
        frontier = new
    return seen


def symmetric(gens, inv):
    out = set(gens)
    for s in gens:
        out.add(inv(s))
    return list(out)


def count_good(A, BR, mul, inv, e):
    AAi = {mul(x, inv(y)) for x in A for y in A}
    good = 0
    for a in A:
        ai = inv(a)
        for h in BR:
            if h == e:
                continue
            if mul(mul(a, h), ai) not in AAi:
                good += 1
                break
    return good


def D(E, BR, mul, inv):
    return {mul(mul(a, h), inv(a)) for a in E for h in BR}


def f2z_test(name, gens, R, M):
    S = symmetric(gens, pinv)
    BR = ball(S, pmul, PE, R)
    z = ((), 1)  # central generator of the Z factor
    E = set()
    x = PE
    for _ in range(M):
        E.add(x)
        x = pmul(x, z)
    DR = D(E, BR, pmul, pinv)
    A = E | DR
    good = count_good(A, BR, pmul, pinv, PE)
    ok = 2 * good < len(A)
    print(f"  {name}: R={R} |B_R|={len(BR)} |E|={len(E)} |D_R(E)\\E|={len(DR - E)}"
          f" |A|={len(A)} good={good}  good<|A|/2: {ok}")
    return ok


# ---------- lamplighter Z/2 wr Z: (frozenset of lit lamps, position) ----------
def lmul(x, y):
    f, k = x
    g, j = y
    return (f ^ frozenset(p + k for p in g), k + j)


def linv(x):
    f, k = x
    return (frozenset(p - k for p in f), -k)


LE = (frozenset(), 0)
LGENS = [(frozenset(), 1), (frozenset({0}), 0)]


def lamp_E(n, ell):
    E = set()
    for bits in itertools.product([0, 1], repeat=n + 1):
        f = frozenset(i for i, b in enumerate(bits) if b)
        for k in range(ell + 1):
            E.add((f, k))
    return E


# ---------- F_2 x lamplighter ----------
def qmul(x, y):
    return (fmul(x[0], y[0]), lmul(x[1], y[1]))


def qinv(x):
    return (finv(x[0]), linv(x[1]))


QE = ((), LE)


def main():
    print("(1) F_2 x Z, E = {z^0..z^(M-1)} central, A = E u D_R(E)")
    allok = True
    prod = [((1,), 0), ((2,), 0), ((), 1)]
    # a non-product generating set: (a,1),(b,0),(a,0); z = (a,1)(a,0)^-1
    skew = [((1,), 1), ((2,), 0), ((1,), 0)]
    for name, gens in [("product S", prod), ("skew S", skew)]:
        for R in (1, 2, 3):
            BR = ball(symmetric(gens, pinv), pmul, PE, R)
            M = len(BR) + 2
            allok &= f2z_test(name, gens, R, M)
    # generation check for skew: the Z-factor element ((),1) must lie in some ball
    Sk = symmetric(skew, pinv)
    found = ((), 1) in ball(Sk, pmul, PE, 6)
    print(f"  skew S generates (z in 6-ball): {found}")
    allok &= found

    print("(2) lamplighter: |D_R(E)| / |E| for E = {(f,k): supp f in [0,n], 0<=k<=ell}")
    LS = symmetric(LGENS, linv)
    for R in (1, 2):
        BR = ball(LS, lmul, LE, R)
        for n, ell in [(4, 4), (4, 16), (4, 64), (6, 64)]:
            E = lamp_E(n, ell)
            DR = D(E, BR, lmul, linv)
            print(f"  R={R} n={n} ell={ell}: |E|={len(E)} |D_R(E)|={len(DR)}"
                  f" ratio={len(DR)/len(E):.4f}")
    print("    F_2 x lamplighter, E = {1} x lamplighter-set, product generators")
    QS = [((1,), LE), ((2,), LE)] + [((), s) for s in LGENS]
    QS = symmetric(QS, qinv)
    for R, n, ell in [(1, 4, 64), (1, 6, 200), (2, 4, 400)]:
        BR = ball(QS, qmul, QE, R)
        E = {((), x) for x in lamp_E(n, ell)}
        DR = D(E, BR, qmul, qinv)
        A = E | DR
        good = count_good(A, BR, qmul, qinv, QE) if len(A) < 6000 else None
        ok = len(DR - E) < len(E)
        print(f"  R={R} n={n} ell={ell}: |E|={len(E)} |D_R(E)\\E|={len(DR - E)}"
              f" killer(|D\\E|<|E|): {ok}  brute good={good} |A|={len(A)}")
        # informational only: the lamplighter sets compress at R=1 but not at
        # R=2 (mixed elements (g,j), g!=0, j!=0, have conjugates
        # ((1+sigma^j) f + sigma^k g, j), injective in (f,k)).  So products
        # with a lamplighter factor are NOT covered by the lemma.

    print("(3) calibration on F_2 (free basis): min over tested E of |D_R(E)\\E|/|E|")
    FS = [(1,), (-1,), (2,), (-2,)]
    rng = random.Random(1)
    for R in (1, 2):
        BR = ball(FS, fmul, (), R)
        worst = 10.0
        tests = []
        tests.append(ball(FS, fmul, (), 3))
        tests.append({(1,) * k for k in range(1, 30)} | {()})
        for _ in range(200):
            m = rng.randint(1, 40)
            E = set()
            for _ in range(m):
                L = rng.randint(0, 6)
                E.add(tuple(rng.choice([1, 2]) for _ in range(L)))
            # reduce words
            E = {fmul((), w) for w in E}
            tests.append(E)
        for E in tests:
            DR = D(E, BR, fmul, finv)
            worst = min(worst, len(DR - E) / len(E))
        print(f"  R={R}: worst ratio {worst:.3f} (>=1 is consistent with CS4 holding on F_2)")
        allok &= worst >= 1.0

    print("ALL CHECKS PASSED" if allok else "SOME CHECK FAILED")


if __name__ == "__main__":
    main()
