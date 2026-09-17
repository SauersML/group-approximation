#!/usr/bin/env python3
"""Sanity check of the height-graded germ model (Theorem A of
research/artifacts/height-graded-germ-models-2026-09-17.md).

Group: G = Z/2 * Z = <z, s | z^2>, elements as reduced normal forms.
Configuration pattern: E = {1, z, s}, F = {1, z, s}.
  Q = {1} u E u FE.  Reads fe = 1: (1,1), (z,z), so m = |F cap E^-1| = 2.
Potential: a(1)=a(z)=0, a(s)=1 ; b(1)=b(z)=0, b(s)=1.  Core K_Z = <z> = {1, z}.

The script
  1. checks that the height ht(1)=0, ht(e)=b(e), ht(fe)=a(f)+b(e) is well defined on Q;
  2. builds the germ model literally: a point at level rho is (rho, c, j) with
     c a coloring of R_rho = K_Z B(rho) by A' and j in [M]^rho; T_f and S_e restrict
     c(f .) to the lower region and truncate j;
  3. checks S_e T_f w == germ of fe for every sampled point w at a top level
     (the identity that makes coincidences of the pattern hold exactly);
  4. estimates the fraction of top-level points whose chart Q -> X is injective
     and compares it with the union bound 1 - |Q|^2/|A'|.
The group here is virtually free (sofic), so this is only a check of the
construction, not new evidence about any nonsofic host.
"""
import random

# ---------- group Z/2 * Z ----------
# normal form: tuple of tokens, 'z' or nonzero int n (s^n), alternating kinds


def mul(u, v):
    st = list(u)
    for t in v:
        if not st:
            st.append(t)
            continue
        top = st[-1]
        if t == 'z' and top == 'z':
            st.pop()
        elif t != 'z' and top != 'z':
            n = top + t
            st.pop()
            if n != 0:
                st.append(n)
        else:
            st.append(t)
    return tuple(st)


ONE = ()
Z = ('z',)
S = (1,)
S_INV = (-1,)


def length(u):
    return sum(1 if t == 'z' else abs(t) for t in u)


def ball(r):
    gens = [Z, S, S_INV]
    seen = {ONE}
    frontier = {ONE}
    for _ in range(r):
        new = set()
        for u in frontier:
            for g in gens:
                w = mul(u, g)
                if w not in seen:
                    new.add(w)
        seen |= new
        frontier = new
    return seen


E = [ONE, Z, S]
F = [ONE, Z, S]
a = {ONE: 0, Z: 0, S: 1}
b = {ONE: 0, Z: 0, S: 1}
CORE = [ONE, Z]
D = max(length(k) for k in CORE)
LAM = 1 + D


def heights():
    ht = {ONE: 0}
    ok = True
    for e in E:
        ok &= ht.setdefault(e, b[e]) == b[e]
    for f in F:
        for e in E:
            p = mul(f, e)
            ok &= ht.setdefault(p, a[f] + b[e]) == a[f] + b[e]
    return ht, ok


HT, CONSISTENT = heights()
Q = list(HT)
L = LAM * max(HT.values())
REGION = {}


def region(rho):
    if rho not in REGION:
        REGION[rho] = {mul(k, g) for k in CORE for g in ball(rho)}
    return REGION[rho]


JUNK = ('junk',)


def restrict(point, g, drop):
    """Germ of point translated by g, at level rho - drop."""
    if point == JUNK:
        return JUNK
    rho, c, j = point
    new = rho - drop
    if new < 0:
        return JUNK
    R = region(new)
    cc = {}
    for h in R:
        gh = mul(g, h)
        if gh not in c:
            raise AssertionError('restriction not defined: g R_new not inside R_rho')
        cc[h] = c[gh]
    return (new, cc, j[:new])


def T(f, point):
    return restrict(point, f, LAM * a[f])


def Sop(e, point):
    return restrict(point, e, LAM * b[e])


def freeze(point):
    if point == JUNK:
        return JUNK
    rho, c, j = point
    return (rho, tuple(sorted((repr(k), v) for k, v in c.items())), j)


def main():
    rng = random.Random(20260917)
    print('pattern heights consistent on Q:', CONSISTENT)
    print('|Q| =', len(Q), ' heights:', sorted(HT.values()))
    reads = [(f, e) for f in F for e in E if mul(f, e) == ONE]
    print('reads fe=1:', len(reads))
    for rho in range(L, L + 2):
        print('level', rho, '|R_rho| =', len(region(rho)))
    for alph in (8, 64, 1024):
        trials = 400
        good = 0
        for _ in range(trials):
            rho = L
            c = {g: rng.randrange(alph) for g in region(rho)}
            j = tuple(rng.randrange(2) for _ in range(rho))
            w = (rho, c, j)
            # exact coincidence identity: S_e T_f w equals germ of fe
            for f in F:
                for e in E:
                    lhs = freeze(Sop(e, T(f, w)))
                    rhs = freeze(restrict(w, mul(f, e), LAM * HT[mul(f, e)]))
                    assert lhs == rhs
            chart = {}
            chart[ONE] = freeze(w)
            for e in E:
                chart.setdefault(e, freeze(Sop(e, w)))
            for f in F:
                for e in E:
                    chart.setdefault(mul(f, e), freeze(Sop(e, T(f, w))))
            if len(set(chart.values())) == len(Q):
                good += 1
        print('A\' size', alph, ' injective-chart fraction', good / trials,
              ' union bound >=', max(0.0, 1 - len(Q) ** 2 / alph))
    print('identity S_e T_f = germ(fe) verified on all samples')


if __name__ == '__main__':
    main()
