#!/usr/bin/env python3
"""Checks for dkkms-ev-list-structure-needs-lists-exponential-in-k.

Part A: Lemma A exhaustively on F_2^m, m <= 5: for every proper subspace W and
        every nonzero functional psi, x uniform on F_2^m \\ W has
        Pr[psi(x) = 0] <= 1/2, with equality iff W is not inside ker psi.
Part B: exact image model of one surjective tuple: X_U = Q = F_2^(n+1),
        Phi = first n coordinates, phi = first l, zeta = next s, x = 0,
        y_d(z) = <d, zeta(z)>.  L' uniform in Gr(Q, l-1), w uniform off L',
        A-label y_(branch of L'+w), B-label y_(branch of L').  For every list
        of t <= 2 functionals (all 2^(n+1) functionals) and for lists drawn from
        the branch assignments with t <= 4, with the best index per L' (the
        index map may depend on L'), the exact ev-uncovered satisfied mass D is
        >= Ddef/2 - (1/2) sum_(d in D_list) Pr[c(L') = <(0,d)>]
        >= Ddef/2 - t 2^(-s-2),   Ddef := mass{c(L') 1-dim, phi(w) notin phi(L')}.
Part C: the numbers of the theorem for 8 <= l <= 64 at k = 3l (worst case),
        exact rationals: value >= 0.605, D > 0.105 for every t < 2^(s-3),
        s = k - l - 8, and the dichotomy exponents.
Exits 0 iff every check passes.
"""
from fractions import Fraction as Fr
import itertools, sys

ok = True


def check(cond, msg):
    global ok
    print(("PASS " if cond else "FAIL ") + msg)
    ok = ok and cond


def par(v):
    return bin(v).count("1") & 1


def span(vs):
    S = {0}
    for v in vs:
        S |= {a ^ v for a in S}
    return frozenset(S)


def subspaces(m):
    """All subspaces of F_2^m, by closure from {0}."""
    seen = {frozenset({0})}
    frontier = list(seen)
    while frontier:
        nxt = []
        for S in frontier:
            for v in range(1, 2 ** m):
                if v not in S:
                    T = frozenset(S | {a ^ v for a in S})
                    if T not in seen:
                        seen.add(T)
                        nxt.append(T)
        frontier = nxt
    return seen


# ---------------------------------------------------------------- Part A
print("Part A: Lemma A (half-agreement off a proper subspace)")
for m in range(1, 6):
    subs = subspaces(m)
    worst = Fr(0)
    eq_ok = True
    for W in subs:
        if len(W) == 2 ** m:
            continue
        comp = [x for x in range(2 ** m) if x not in W]
        for psi in range(1, 2 ** m):
            pr = Fr(sum(1 for x in comp if par(psi & x) == 0), len(comp))
            worst = max(worst, pr)
            inside = all(par(psi & w) == 0 for w in W)
            if (pr == Fr(1, 2)) == inside:
                eq_ok = False
    check(worst <= Fr(1, 2), f"m={m}: max Pr[psi(x)=0 | x notin W] = {worst} <= 1/2")
    check(eq_ok, f"m={m}: equality 1/2 exactly when W is not inside ker psi")


# ---------------------------------------------------------------- Part B
def part_b(l, s):
    n = l + s
    dq = n + 1
    lo = (1 << l) - 1
    nm = (1 << n) - 1
    grass = [S for S in subspaces(dq) if len(S) == 2 ** (l - 1)]

    def branch(S):
        c = {z & nm for z in S if (z & nm) != 0 and (z & lo) == 0}
        return (next(iter(c)) >> l) if len(c) == 1 else 0

    funcs = list(range(2 ** dq))
    nL = len(grass)
    # per L': list of (w, satisfied, A-ev bit, in E_def)
    data = []
    ddef = Fr(0)
    pd = {}
    for Lp in grass:
        dB = branch(Lp)
        fB = dB << l
        basis = [v for v in Lp if v]
        phiL = {z & lo for z in Lp}
        ws = [w for w in range(2 ** dq) if w not in Lp]
        rows = []
        for w in ws:
            L = frozenset(Lp | {a ^ w for a in Lp})
            fA = branch(L) << l
            sat = all(par((fA ^ fB) & v) == 0 for v in basis)
            edef = dB != 0 and (w & lo) not in phiL
            rows.append((w, sat, par(fA & w), edef))
            if edef:
                ddef += Fr(1, nL * len(ws))
        if dB:
            pd[dB] = pd.get(dB, 0) + Fr(1, nL)
        data.append(rows)
    satm = [Fr(sum(1 for r in rows if r[1]), len(rows)) for rows in data]
    cov = {}
    for lam in funcs:
        cov[lam] = [Fr(sum(1 for (w, st, ev, _) in rows if st and par(lam & w) == ev),
                       len(rows)) for rows in data]
    sat_total = sum(satm) / nL

    def D_of(lst):
        return sat_total - sum(max(cov[lam][j] for lam in lst) for j in range(nL)) / nL

    def bound(lst):
        dset = {lam >> l for lam in lst if lam & ~(((1 << s) - 1) << l) == 0 and lam}
        return ddef / 2 - sum(pd.get(d, 0) for d in dset) / 2

    worst_gap = None
    ok_all = True
    lists = [(a,) for a in funcs] + list(itertools.combinations(funcs, 2))
    brs = [d << l for d in range(2 ** s)]
    for t in range(3, min(4, len(brs)) + 1):
        lists += list(itertools.combinations(brs, t))
    for lst in lists:
        Dv = D_of(lst)
        b = bound(lst)
        weak = ddef / 2 - len(lst) * Fr(1, 2 ** (s + 2))
        if not (Dv >= b >= weak):
            ok_all = False
        g = Dv - b
        worst_gap = g if worst_gap is None else min(worst_gap, g)
    check(max(pd.values()) < Fr(1, 2 ** (s + 1)), f"(l,s)=({l},{s}): max_d Pr[c(L')=<(0,d)>] < 2^(-s-1)")
    check(ok_all, f"(l,s)=({l},{s}): D >= Ddef/2 - (1/2)sum_D Pr >= Ddef/2 - t 2^(-s-2) "
                  f"on {len(lists)} lists; Ddef={float(ddef):.4f}, min slack={float(worst_gap):.4f}")


print("Part B: exact image model, best index per L'")
part_b(3, 2)
part_b(4, 1)


# ---------------------------------------------------------------- Part C
def nullity_law(l):
    """Limit law of N (as in the LS artifact, d' -> oo): stay prob 2^(r-l)."""
    dist = {0: Fr(1)}
    for i in range(l - 1):
        new = {}
        for r, p in dist.items():
            stay = Fr(2 ** r, 2 ** l)
            new[r] = new.get(r, 0) + p * stay
            new[r + 1] = new.get(r + 1, 0) + p * (1 - stay)
        dist = new
    return {(l - 1) - r: p for r, p in dist.items()}


print("Part C: numbers at k = 3l, s = k - l - 8 (n = k - 8), t < 2^(s-3)")
allc = True
for l in range(8, 65):
    k = 3 * l
    s = k - l - 8
    law = nullity_law(l)
    p1 = law.get(1, 0)
    v = 1 - sum(p * Fr(1, 2 ** (1 + nn)) for nn, p in law.items())
    beta_bad = Fr(1, 2 ** 8) / (1 - Fr(2 ** (l - 1), 2 ** k))   # delta_sur < 2^(n-k)
    o_val = Fr(1, 2 ** (k - l)) + beta_bad                       # LS Step 6
    o_D = Fr(3, 8) * (Fr(1, 2 ** (k - l)) + Fr(1, 2 ** (s + 1)) + beta_bad)
    val_lb = v - o_val
    D_lb = Fr(3, 8) * p1 - Fr(1, 32) - o_D                        # t 2^(-s-2) < 1/32
    good = val_lb >= Fr(605, 1000) and D_lb > Fr(105, 1000)
    good = good and (k - 2 * l - 5 < s - 3) and (k / 2 - l - Fr(5, 2) < s - 3)
    allc = allc and good
    if l in (8, 12, 16, 32, 64):
        print(f"  l={l:2d} k={k:3d} s={s:3d}  P(N=1)={float(p1):.6f}  val>={float(val_lb):.5f}"
              f"  D>{float(D_lb):.5f}")
check(allc, "8<=l<=64, k=3l: val >= 0.605, D > 0.105 for t < 2^(s-3), "
            "and both (S) exponents k-2l-5, k/2-l-5/2 are below s-3")
print("Monotone in k: 2^(l-k), 2^(-s-1) and the beta_bad bound all decrease as k grows.")

sys.exit(0 if ok else 1)
