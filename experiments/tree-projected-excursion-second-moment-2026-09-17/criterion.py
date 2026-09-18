#!/usr/bin/env python3
"""Excursion second-moment criterion for tree-projected Cayley graphs of F_n x Z.

Ensemble: decorated paths over a reduced word t_1..t_N; before each step t_(i+1)
(i >= 1) an optional depth-one excursion g -> g u -> g u u'^(-1) along a letter
e != t_i^(-1), with u != u' in S_e, and no backtracking (s_(i+1) != u' if e = t_(i+1)).

For a pair of paths following a common prefix, one block = slot + step. The script
bounds, for Z = F_n x Z with m decorations per letter (heights arbitrary), the
lumped transfer matrix
    T = [[alpha, beta], [gamma, delta]]
(state 0: both paths at the same vertex; state 1: same fibre, different vertex),
with weights p^(#edges) x^(#shared edges), x = 1/p, using the counting bound
    #{choices satisfying a linear system of rank r in k decoration variables}
        <= m^(components) (m-1)^(forest edges)
(a spanning forest of the inequality graph u != u', s != u' on a free-variable set
complementary to r independent columns; components + forest edges = k - r),
the removal of configurations whose equations force an inequality (or h = 0) to fail,
and the inclusion identity  sum x^sh = sum_Q (x-1)^|Q| #{Q subset sh}.
Criterion: rho(T) < b w^2, with w the exact one-path block weight.
All arithmetic is exact (Fractions).
"""
from fractions import Fraction as F
from itertools import combinations
import sys

VARS = ['u', 'v', 's', 'U', 'V', 'S', 'h']  # v = u', U = sigma, V = sigma', S = s'


def form(**kw):
    return {k: F(c) for k, c in kw.items() if c}


def add(*fs):
    r = {}
    for f in fs:
        for k, c in f.items():
            r[k] = r.get(k, 0) + c
    return {k: c for k, c in r.items() if c}


def neg(f):
    return {k: -c for k, c in f.items()}


def rank(rows, cols):
    M = [[r.get(c, F(0)) for c in cols] for r in rows]
    rk = 0
    ncol = len(cols)
    for c in range(ncol):
        piv = None
        for i in range(rk, len(M)):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        for i in range(len(M)):
            if i != rk and M[i][c] != 0:
                f = M[i][c] / M[rk][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[rk])]
        rk += 1
    return rk


def path(kind, primed, letter):
    """Return (vars, edges, next-height form, inequality forms, #edges)."""
    if not primed:
        u, v, s, base = 'u', 'v', 's', {}
    else:
        u, v, s, base = 'U', 'V', 'S', form(h=1)
    fu, fv, fs = form(**{u: 1}), form(**{v: 1}), form(**{s: 1})
    if kind == 'none':
        nxt = add(base, fs)
        return [s], [('t', base, nxt)], nxt, [], 1
    plus = add(base, fu, neg(fv))
    y = add(base, fu)
    nxt = add(plus, fs)
    lab = 't' if kind == 'Et' else letter
    edges = [(lab, base, y), (lab, plus, y), ('t', plus, nxt)]
    ineq = [add(fu, neg(fv))]
    if kind == 'Et':
        ineq.append(add(fs, neg(fv)))
    return [u, v, s], edges, nxt, ineq, 3


def pair_types(E):
    return [
        ('none', None, 'none', None, 1),
        ('none', None, 'Et', None, 1),
        ('none', None, 'Eo', 'e1', E - 1),
        ('Et', None, 'none', None, 1),
        ('Et', None, 'Et', None, 1),
        ('Et', None, 'Eo', 'e1', E - 1),
        ('Eo', 'e1', 'none', None, E - 1),
        ('Eo', 'e1', 'Et', None, E - 1),
        ('Eo', 'e1', 'Eo', 'e1', E - 1),
        ('Eo', 'e1', 'Eo', 'e2', (E - 1) * (E - 2)),
    ]


def count_bound(rows, vars_, ineqs):
    """Bound #solutions by m^(components) (m-1)^(forest edges) of the inequality graph
    on a set of free variables whose complement is determined by the system."""
    k = len(vars_)
    r = rank(rows, vars_)
    best = (k - r, 0)
    pairs = []
    for f in ineqs:
        ks = [a for a in f if a != 'h']
        if len(ks) == 2 and f.get('h', 0) == 0:
            pairs.append(tuple(ks))
    for free in combinations(vars_, k - r):
        det = [a for a in vars_ if a not in free]
        if rank(rows, det) != r:
            continue
        # forest edges among free vars
        parent = {a: a for a in free}

        def find(a):
            while parent[a] != a:
                a = parent[a]
            return a
        fe = 0
        for (a, c) in pairs:
            if a in parent and c in parent:
                ra, rc = find(a), find(c)
                if ra != rc:
                    parent[ra] = rc
                    fe += 1
        cand = (k - r - fe, fe)
        if cand[1] > best[1]:
            best = cand
    return best


def implied(rows, f, cols):
    return rank(rows + [f], cols) == rank(rows, cols)


def terms(E, excursions=True):
    """Symbolic terms: list of (state, target, mult, nedges, nshared_subset, dim)."""
    out = []
    for state in (0, 1):
        cols_full = VARS if state == 1 else VARS[:-1]
        for (k1, l1, k2, l2, mult) in pair_types(E):
            if not excursions and (k1 != 'none' or k2 != 'none'):
                continue
            v1, e1, n1, q1, ne1 = path(k1, False, l1)
            v2, e2, n2, q2, ne2 = path(k2, True, l2)
            vars_ = v1 + v2
            k = len(vars_)
            ineqs = q1 + q2
            ret = add(n1, neg(n2))
            if state == 0:
                ret = {a: c for a, c in ret.items() if a != 'h'}
            cands = []
            for a in e1:
                for b in e2:
                    if a[0] == b[0]:
                        eqs = [add(a[1], neg(b[1])), add(a[2], neg(b[2]))]
                        if state == 0:
                            eqs = [{x: c for x, c in q.items() if x != 'h'} for q in eqs]
                        cands.append([q for q in eqs if q])
            for r in range(len(cands) + 1):
                for Q in combinations(range(len(cands)), r):
                    rows = [q for i in Q for q in cands[i]]

                    def forced(rows_):
                        if any(implied(rows_, f, cols_full) for f in ineqs):
                            return True
                        if state == 1 and implied(rows_, form(h=1), cols_full):
                            return True
                        return False
                    base_forced = forced(rows)
                    if base_forced:
                        continue
                    # to state 0
                    rows0 = rows + [ret]
                    if not forced(rows0):
                        d = count_bound(rows0, vars_, ineqs)
                        out.append((state, 0, mult, ne1 + ne2, len(Q), d))
                    # to state 1
                    if not implied(rows, ret, cols_full):
                        d = count_bound(rows, vars_, ineqs)
                        out.append((state, 1, mult, ne1 + ne2, len(Q), d))
    return out


def matrix(TERMS, m, p):
    x = 1 / p
    T = [[F(0), F(0)], [F(0), F(0)]]
    for (st, tg, mult, ne, nq, d) in TERMS:
        comps, fedges = d
        T[st][tg] += mult * p ** ne * (x - 1) ** nq * F(m) ** comps * F(m - 1) ** fedges
    return T


def wblock(n, m, p, excursions=True):
    E = 2 * n - 1
    w = m * p
    if excursions:
        w += (E - 1) * m * m * (m - 1) * p ** 3 + m * (m - 1) ** 2 * p ** 3
    return w


def criterion(TERMS, n, m, p, excursions=True):
    b = 2 * n - 1
    T = matrix(TERMS, m, p)
    w = wblock(n, m, p, excursions)
    L = b * w * w
    (al, be), (ga, de) = T
    ok = L > al and L > de and (L - al) * (L - de) > be * ga
    return ok, T, w, L


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    TE = terms(2 * n - 1, True)
    print('terms', len(TE))
    for m in [3, 5, 10, 20, 50]:
        for p in [F(1, 4 * m), F(27, 100 * m), F(28, 100 * m)]:
            ok, T, w, L = criterion(TE, n, m, p)
            print(m, float(p * m), ok, [[float(a) for a in r] for r in T], float(w), float(L))
