#!/usr/bin/env python3
"""Second-moment engine for rank-two tree-projected Cayley graphs of F_2 x Z.

Ensemble ("slot trails").  A trail follows a reduced word t_1..t_N.  Before step i+1
(i >= 1) it runs a slot in the fibre of w_i: an optional vertical step z -> z+c along a
FIXED vertical generator (1,c), then up to J depth-one excursions
z -> (w_i e, z+u) -> (w_i, z+u-u') along letters e != t_i^-1 with u != u' in D_e, and
u_(j+1) != u'_j when two consecutive excursions use the same letter, and s != u'_last
when the last excursion uses t_(i+1).  Data whose block has two equal edges are
excluded from the ensemble (their number is subtracted in the first moment and they
are simply over-counted in the second moment).

Pair transfer.  Offsets h of path 2 relative to path 1 in a common fibre are classified
as h = k c (|k| <= K) or 'generic'.  For each class s and each target class the one-block
pair sum is bounded by a finite sum of terms
    p^(#edges) (x-1)^(|Q|) m^comps (m-1)^fedges
(inclusion identity over sets Q of candidate shared-edge pairs; counting bound of
fpbs-tree-projected-rank-two-excursion-second-moment-proof, section 3).  The extra
target 'NZ' bounds the total mass into all nonzero classes (no class equation).

Exact rational arithmetic throughout (Fractions).
"""
from fractions import Fraction as F
from itertools import combinations, product
import sys

LETTERS = ['t', 'o1', 'o2']      # letters available in the fibre (t = next step letter)


# ---------------------------------------------------------------- linear algebra
def reduce_vec(v, rref):
    """rref: list of (pivot, row) with row[pivot] = 1; reduce v (dict)."""
    v = dict(v)
    for piv, row in rref:
        a = v.get(piv, 0)
        if a:
            for k, c in row.items():
                nv = v.get(k, 0) - a * c
                if nv:
                    v[k] = nv
                else:
                    v.pop(k, None)
    return v


def rref_add(rref, v, order):
    """Return new rref with v added (or the same object if v is dependent)."""
    r = reduce_vec(v, rref)
    if not r:
        return rref, False
    piv = min(r, key=order.index)
    a = r[piv]
    r = {k: c / a for k, c in r.items()}
    new = []
    for p2, row in rref:
        b = row.get(piv, 0)
        if b:
            row = dict(row)
            for k, c in r.items():
                nv = row.get(k, 0) - b * c
                if nv:
                    row[k] = nv
                else:
                    row.pop(k, None)
        new.append((p2, row))
    new.append((piv, r))
    return new, True


def rref_key(rref):
    return tuple(sorted((p, tuple(sorted(r.items()))) for p, r in rref))


def rank_cols(rows, cols):
    M = [[r.get(c, F(0)) for c in cols] for r in rows]
    rk = 0
    for ci in range(len(cols)):
        piv = None
        for i in range(rk, len(M)):
            if M[i][ci] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        for i in range(len(M)):
            if i != rk and M[i][ci] != 0:
                f = M[i][ci] / M[rk][ci]
                M[i] = [a - f * b for a, b in zip(M[i], M[rk])]
        rk += 1
    return rk


def add(*fs):
    r = {}
    for f in fs:
        for k, c in f.items():
            r[k] = r.get(k, 0) + c
    return {k: c for k, c in r.items() if c}


def neg(f):
    return {k: -c for k, c in f.items()}


def var(name):
    return {name: F(1)}


# ---------------------------------------------------------------- paths
def slot_structures(J, vertical):
    out = []
    for V in ([0, 1] if vertical else [0]):
        for j in range(J + 1):
            for seq in product(LETTERS, repeat=j):
                out.append((V, seq))
    return out


def build_path(struct, primed):
    """Return dict with vars, domains, edges, end form, simple ineqs, internal coincidence systems."""
    V, seq = struct
    P = 'P' if primed else 'p'
    base = var('h') if primed else {}
    vars_, dom, edges, ineq = [], {}, [], []
    z = base
    if V:
        top = add(z, var('c'))
        edges.append(('vert', z, top))
        z = top
    prev = None
    for j, e in enumerate(seq):
        u, v = '%su%d' % (P, j), '%sv%d' % (P, j)
        vars_ += [u, v]
        dom[u] = dom[v] = e
        y = add(z, var(u))
        z2 = add(y, neg(var(v)))
        edges.append((e, z, y))
        edges.append((e, z2, y))
        ineq.append((u, v))
        if prev is not None and prev[0] == e:
            ineq.append((u, prev[1]))
        prev = (e, v)
        z = z2
    s = P + 's'
    vars_.append(s)
    dom[s] = 't'
    end = add(z, var(s))
    edges.append(('t', z, end))
    if prev is not None and prev[0] == 't':
        ineq.append((s, prev[1]))
    internal = []
    for a, b in combinations(edges, 2):
        if a[0] == b[0]:
            internal.append([add(a[1], neg(b[1])), add(a[2], neg(b[2]))])
    return dict(vars=vars_, dom=dom, edges=edges, end=end, ineq=ineq,
                internal=internal, ne=len(edges))


def subst(f, hval):
    """hval: None (keep h) or integer k meaning h = k c."""
    if hval is None or 'h' not in f:
        return f
    f = dict(f)
    a = f.pop('h')
    return add(f, {'c': a * hval})


# ---------------------------------------------------------------- counting
_cb_memo = {}


def count_bound(rows, vars_, ineqs, key=None):
    if key is not None and key in _cb_memo:
        return _cb_memo[key]
    k = len(vars_)
    r = rank_cols(rows, vars_)
    best = (k - r, 0)
    for free in combinations(vars_, k - r):
        det = [a for a in vars_ if a not in free]
        if det and rank_cols(rows, det) != r:
            continue
        parent = {a: a for a in free}

        def find(a):
            while parent[a] != a:
                a = parent[a]
            return a
        fe = 0
        for (a, c) in ineqs:
            if a in parent and c in parent:
                ra, rc = find(a), find(c)
                if ra != rc:
                    parent[ra] = rc
                    fe += 1
        if fe > best[1]:
            best = (k - r - fe, fe)
    if key is not None:
        _cb_memo[key] = best
    return best


def exact_count_simple(vars_, ineqs):
    """Number of assignments with values in m-sets satisfying the simple (forest) ineqs:
    returns (comps, fedges) exactly (the ineq graph is a forest of paths)."""
    parent = {a: a for a in vars_}

    def find(a):
        while parent[a] != a:
            a = parent[a]
        return a
    fe = 0
    for (a, c) in ineqs:
        ra, rc = find(a), find(c)
        assert ra != rc, 'simple inequality graph must be a forest'
        parent[ra] = rc
        fe += 1
    return (len(vars_) - fe, fe)


# ---------------------------------------------------------------- one-path block weight
def first_moment_terms(J, vertical):
    """List of (ne, sign, (comps, fedges)) giving a lower bound for the one-block weight."""
    out = []
    for st in slot_structures(J, vertical):
        P = build_path(st, False)
        vars_, ineqs = P['vars'], P['ineq']
        order = vars_ + ['h', 'c']
        out.append((P['ne'], 1, exact_count_simple(vars_, ineqs)))
        for sysm in P['internal']:
            rows = [q for q in sysm if q]
            rr = []
            for q in rows:
                rr, _ = rref_add(rr, q, order)
            bad = False
            for (a, b) in ineqs:
                if not reduce_vec(add(var(a), neg(var(b))), rr):
                    bad = True
            if not reduce_vec(var('c'), rr):
                bad = True
            if bad:
                continue
            out.append((P['ne'], -1, count_bound([r for _, r in rr], vars_, ineqs)))
    return out


def wblock(FM, m, p):
    w = F(0)
    for ne, sg, (cm, fe) in FM:
        w += sg * p ** ne * F(m) ** cm * F(m - 1) ** fe
    return w


# ---------------------------------------------------------------- pair terms
def pair_terms(J, K, vertical=True, verbose=False):
    specials = list(range(-K, K + 1))
    classes = specials + ['G']
    ncl = len(classes)
    NZ = ncl
    structs = slot_structures(J, vertical)
    agg = {}   # (si, ti, ne, nq, comps, fedges) -> multiplicity
    for si, cl in enumerate(classes):
        hval = None if cl == 'G' else cl
        for s1 in structs:
            P1 = build_path(s1, False)
            for s2 in structs:
                P2 = build_path(s2, True)
                vars_ = P1['vars'] + P2['vars']
                order = vars_ + ['h', 'c']
                ineqs = P1['ineq'] + P2['ineq']
                ne = P1['ne'] + P2['ne']
                hp = subst(add(P2['end'], neg(P1['end'])), hval)
                cands = []
                for a in P1['edges']:
                    for b in P2['edges']:
                        if a[0] == b[0]:
                            eqs = [subst(add(a[1], neg(b[1])), hval), subst(add(a[2], neg(b[2])), hval)]
                            cands.append([q for q in eqs if q])
                forbid = [add(var(a), neg(var(b))) for (a, b) in ineqs] + [var('c')]
                if cl == 'G':
                    forbid += [add(var('h'), {'c': F(-k)}) for k in specials]
                internal = [[subst(q, hval) for q in sm] for sm in (P1['internal'] + P2['internal'])]

                def is_forced(rr):
                    for f in forbid:
                        if not reduce_vec(f, rr):
                            return True
                    for sm in internal:
                        if all(not reduce_vec(q, rr) for q in sm):
                            return True
                    return False
                # DFS over subsets of candidates, grouped by row space
                groups = {}

                def dfs(i, rr, nq):
                    if i == len(cands):
                        key = rref_key(rr)
                        g = groups.setdefault(key, [rr, {}])
                        g[1][nq] = g[1].get(nq, 0) + 1
                        return
                    dfs(i + 1, rr, nq)
                    r2 = rr
                    for q in cands[i]:
                        r2, _ = rref_add(r2, q, order)
                    if not is_forced(r2):
                        dfs(i + 1, r2, nq + 1)
                if is_forced([]):
                    continue
                dfs(0, [], 0)
                for key, (rr, nqs) in groups.items():
                    rows = [r for _, r in rr]
                    targets = []
                    for ti, k in enumerate(specials):
                        eq = add(hp, {'c': F(-k)})
                        r2 = rr
                        if eq:
                            r2, _ = rref_add(rr, eq, order)
                        if is_forced(r2):
                            continue
                        targets.append((ti, r2))
                    # generic target: drop if h' forced into a special class
                    bad = any(not reduce_vec(add(hp, {'c': F(-k)}), rr) for k in specials)
                    if not bad:
                        targets.append((ncl - 1, rr))
                    if hp and reduce_vec(hp, rr):
                        targets.append((NZ, rr))
                    for ti, r2 in targets:
                        rws = [r for _, r in r2]
                        d = count_bound(rws, vars_, ineqs,
                                        key=(rref_key(r2), tuple(vars_), tuple(ineqs)))
                        for nq, mult in nqs.items():
                            kk = (si, ti, ne, nq, d[0], d[1])
                            agg[kk] = agg.get(kk, 0) + mult
        if verbose:
            print('class', cl, 'done; aggregated terms', len(agg), flush=True)
    return [(k[0], k[1], v, k[2], k[3], (k[4], k[5])) for k, v in agg.items()], ncl


def matrix(TERMS, ncl, m, p):
    x = 1 / p
    T = [[F(0)] * (ncl + 1) for _ in range(ncl)]
    for (st, tg, mult, ne, nq, d) in TERMS:
        comps, fedges = d
        T[st][tg] += mult * p ** ne * (x - 1) ** nq * F(m) ** comps * F(m - 1) ** fedges
    return T


def phi(T, y, zero):
    """Monotone LP bound: row s -> T[s][zero] y[zero] + max sum_j mass_j y_j over the
    nonzero classes j, subject to mass_j <= T[s][j], sum_j mass_j <= T[s][NZ]."""
    ncl = len(T)
    others = sorted([j for j in range(ncl) if j != zero], key=lambda j: -y[j])
    out = []
    for s in range(ncl):
        tot = T[s][zero] * y[zero]
        cap = T[s][ncl]
        for j in others:
            a = min(T[s][j], cap)
            if a <= 0:
                break
            tot += a * y[j]
            cap -= a
        out.append(tot)
    return out


def rho_phi(T, zero, it=300):
    Tf = [[float(a) for a in r] for r in T]
    ncl = len(T)
    y = [1.0] * ncl
    for _ in range(it):
        z = phi(Tf, y, zero)
        mx = max(z)
        y = [a / mx for a in z]
    z = phi(Tf, y, zero)
    return max(z[i] / y[i] for i in range(ncl)), y


def certify(T, zero, L):
    """Exact Collatz-Wielandt check: positive rational y with phi(y) < L y."""
    lam, y = rho_phi(T, zero)
    yq = [F(max(a, 1e-9)).limit_denominator(10 ** 6) for a in y]
    z = phi(T, yq, zero)
    return all(z[i] < L * yq[i] for i in range(len(T))), lam / float(L)
