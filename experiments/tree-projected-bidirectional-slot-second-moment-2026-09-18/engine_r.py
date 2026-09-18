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

Bidirectional extension (this file; w5-009's engine.py is the case R = (0, 1)).  The
optional vertical step is replaced by a vertical run r in R (r > 0: r steps z -> z + c,
r < 0: |r| steps z -> z - c; both along generators of the vertical part {(1, +-c)}).
The fibre-vertical edge of either direction is represented as ('vert', lower, upper), so
an up-step of one path and a down-step of the other can share an edge.

Optional refinements (module flags, default off; see the -proof node):
  NZREF  -- refined NZ capacity: subtract from each NZ term the EXACT number of pairs
            satisfying the same shared-edge equations with h' = 0 (only when that count
            is an exact forest count and no internal coincidence is compatible).
  RIGID  -- rigid-decoration counting: a determined variable y = a x + gam with a single
            free x gains m -> m - 1 (valid when D_a, -D_a, D_b, -D_b are pairwise
            non-translates, and gam guaranteed != 0 where needed).
  RIGID2 -- multi-variable version of RIGID (tiny gain; not used in the certificate).

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
def runs_of(vertical):
    """vertical: True -> (0, 1) (w5-009), False -> (0,), or an explicit tuple of runs r
    (r > 0: r steps z -> z + c; r < 0: |r| steps z -> z - c)."""
    if vertical is True:
        return (0, 1)
    if vertical is False:
        return (0,)
    return tuple(vertical)


POST = (0,)   # vertical runs allowed after the last excursion (before the step s)


def slot_structures(J, vertical):
    out = []
    for V in runs_of(vertical):
        for j in range(J + 1):
            for seq in product(LETTERS, repeat=j):
                for V2 in (POST if j else (0,)):
                    out.append((V, seq, V2))
    return out


def vrun(z, V, edges):
    """Append a vertical run of V steps (V < 0: downward) starting at height z."""
    for _ in range(abs(V)):
        if V > 0:
            top = add(z, var('c'))
            edges.append(('vert', z, top))
            z = top
        else:
            bot = add(z, {'c': F(-1)})
            edges.append(('vert', bot, z))
            z = bot
    return z


def build_path(struct, primed):
    """Return dict with vars, domains, edges, end form, simple ineqs, internal coincidence systems."""
    V, seq, V2 = struct
    P = 'P' if primed else 'p'
    base = var('h') if primed else {}
    vars_, dom, edges, ineq = [], {}, [], []
    z = base
    z = vrun(z, V, edges)
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
    z = vrun(z, V2, edges)
    s = P + 's'
    vars_.append(s)
    dom[s] = 't'
    end = add(z, var(s))
    edges.append(('t', z, end))
    if prev is not None and prev[0] == 't' and V2 == 0:
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


RIGID = False


def _express(rows, det):
    """Solve rows for the variables det; return {d: expression in the others} or None."""
    M = [dict(r) for r in rows]
    used = set()
    piv = {}
    for d in det:
        i = next((i for i in range(len(M)) if i not in used and M[i].get(d, 0)), None)
        if i is None:
            return None
        used.add(i)
        a = M[i][d]
        M[i] = {k: c / a for k, c in M[i].items()}
        for j in range(len(M)):
            b = M[j].get(d, 0)
            if j != i and b:
                M[j] = add(M[j], {k: -b * c for k, c in M[i].items()})
        piv[d] = i
    return {d: {k: -c for k, c in M[i].items() if k != d} for d, i in piv.items()}


def _nonzero(gam, K, generic):
    """Is the constant gam = alpha c + beta h nonzero for every admissible (c, h)?
    c != 0 always; in the generic class h != k c for |k| <= K."""
    al, be = gam.get('c', F(0)), gam.get('h', F(0))
    if not be:
        return al != 0
    if not generic:
        return False
    k = -al / be
    return k.denominator == 1 and abs(k) <= K


def restricted(expr_y, dy, dom, K, generic):
    """If y = a x + gam with x a single free variable, return x when the number of x in
    D_x with a x + gam in D_y is at most m - 1 for every RIGID decoration; else None.
    Rigidity: D_a, -D_a, D_b, -D_b pairwise distinct up to translation, so
      a = +1, different letters: D_y = D_x + g is impossible (also for inverse letters);
      a = -1, same letter:       D = -D + g is impossible;
      a = +1, same letter:       fails only for g = 0;
      a = -1, different letters: fails only for g = 0 (inverse letters, D_y = -D_x);
      |a| != 1, same letter:     a x + g maps D onto D only if |a| = 1 (diameters).
    """
    xs = [k for k in expr_y if k not in ('h', 'c')]
    if len(xs) != 1:
        return None
    x = xs[0]
    a = expr_y[x]
    gam = {k: v for k, v in expr_y.items() if k in ('h', 'c')}
    same = dom[x] == dy
    if a == 1:
        ok = (not same) or _nonzero(gam, K, generic)
    elif a == -1:
        ok = same or _nonzero(gam, K, generic)
    else:
        ok = same
    return x if ok else None


RIGID2 = False


def restricted_multi(expr_y, dy, dom):
    """y = a x + (other free variables) + gam.  With the other free variables fixed, the
    number of x in D_x with y in D_y is <= m - 1 for every rigid decoration whenever
    a = +1 and the letters differ, a = -1 and the letters agree, or |a| != 1 and the letters
    agree (the constant is then arbitrary).  Returns the list of (x, others)."""
    xs = [k for k in expr_y if k not in ('h', 'c')]
    out = []
    if len(xs) < 2:
        return out
    for x in xs:
        a = expr_y[x]
        same = dom[x] == dy
        if (a == 1 and not same) or (a == -1 and same) or (abs(a) != 1 and same):
            out.append((x, set(xs) - {x}))
    return out


def gain_order(cand, find, free):
    """Number of trees counted m-1 instead of m.  Trees are counted in an order; a tree
    gains when it contains a candidate x whose other variables lie in trees counted
    before it (x is then the root of its tree and ranges over at most m - 1 values).
    Greedy: first all trees without candidates, then repeatedly any tree that can gain."""
    trees = {find(a) for a in free}
    ct = {}
    for x, oth in cand:
        ct.setdefault(find(x), []).append({find(o) for o in oth})
    done = {t for t in trees if t not in ct}
    g = 0
    rest = set(ct)
    while rest:
        pick = None
        for t in sorted(rest):
            if any(t not in S and S <= done for S in ct[t]):
                pick = t
                break
        if pick is None:
            break
        done.add(pick)
        rest.discard(pick)
        g += 1
    return g


def count_bound_rig(rows, vars_, ineqs, dom, K, generic, key=None):
    """As count_bound, but each tree of the inequality forest (on the free variables) that
    contains a restricted free variable (see restricted) is counted m-1 instead of m for its
    root: valid for rigid decorations.  Returns (comps, fedges) of m^comps (m-1)^fedges."""
    if key is not None and key in _cb_memo:
        return _cb_memo[key]
    rows = [r for r in rows if any(k not in ('h', 'c') for k in r)]
    k = len(vars_)
    r = rank_cols(rows, vars_)
    best = (k - r, 0)
    for free in combinations(vars_, k - r):
        det = [a for a in vars_ if a not in free]
        if det and rank_cols(rows, det) != r:
            continue
        ex = _express(rows, det) if det else {}
        if ex is None:
            continue
        cand = []     # (x, other free variables of the expression)
        for d, e in ex.items():
            x = restricted(e, dom[d], dom, K, generic)
            if x is not None:
                cand.append((x, set()))
            elif RIGID2:
                cand += restricted_multi(e, dom[d], dom)
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
        g = gain_order(cand, find, free)
        if fe + g > best[1]:
            best = (k - r - fe - g, fe + g)
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
                dom = {}
                dom.update(P1['dom']); dom.update(P2['dom'])
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
                        if NZREF:
                            # subtract an exact lower bound for the pairs of this term
                            # that end at h' = 0 (they are not in the nonzero classes)
                            r0, _ = rref_add(rr, hp, order)
                            def no_internal(r0):
                                # every internal coincidence of a solution of r0 must force a
                                # forbidden equality, so that the exact count below counts
                                # ensemble pairs only
                                for sm in internal:
                                    r3 = r0
                                    for q in sm:
                                        r3, _ = rref_add(r3, q, order)
                                    if not any(not reduce_vec(f, r3) for f in forbid):
                                        return False
                                return True
                            if not is_forced(r0) and no_internal(r0):
                                lb = identity_lower(r0, vars_, ineqs, dom)
                                if lb is not None:
                                    for nq, mult in nqs.items():
                                        kk = (si, NZ, ne, nq, lb[0], lb[1])
                                        agg[kk] = agg.get(kk, 0) - mult
                    for ti, r2 in targets:
                        rws = [r for _, r in r2]
                        if RIGID:
                            d = count_bound_rig(rws, vars_, ineqs, dom, K, cl == 'G',
                                                key=('rig', RIGID2, rref_key(r2), tuple(vars_), tuple(ineqs),
                                                     tuple(sorted(dom.items())), K, cl == 'G'))
                        else:
                            d = count_bound(rws, vars_, ineqs,
                                            key=(rref_key(r2), tuple(vars_), tuple(ineqs)))
                        for nq, mult in nqs.items():
                            kk = (si, ti, ne, nq, d[0], d[1])
                            agg[kk] = agg.get(kk, 0) + mult
        if verbose:
            print('class', cl, 'done; aggregated terms', len(agg), flush=True)
    return [(k[0], k[1], v, k[2], k[3], (k[4], k[5])) for k, v in agg.items()], ncl


NZREF = False


def identity_lower(rr, vars_, ineqs, dom):
    """Exact count m^comps (m-1)^fedges of the solutions of the system rr in D^vars
    subject to the inequalities, valid for EVERY decoration, when every row of rr is
    x - y = 0 with x, y variables of the same letter (so the system only identifies
    variables) and the identified inequality graph is a forest.  Returns None when this
    does not apply (then no lower bound is used)."""
    parent = {a: a for a in vars_}

    def find(a):
        while parent[a] != a:
            a = parent[a]
        return a
    for _, row in rr:
        if len(row) != 2 or any(k not in parent for k in row):
            return None
        (x, a), (y, b) = row.items()
        if a + b != 0 or dom[x] != dom[y]:
            return None
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[rx] = ry
    roots = {find(a) for a in vars_}
    fe = 0
    edges = set()
    for (a, b) in ineqs:
        ra, rb = find(a), find(b)
        if ra == rb:
            return None
        edges.add(frozenset((ra, rb)))
    p2 = {r: r for r in roots}

    def f2(a):
        while p2[a] != a:
            a = p2[a]
        return a
    for e in edges:
        ra, rb = tuple(e)
        x, y = f2(ra), f2(rb)
        if x == y:
            return None          # a cycle: the forest formula is not a lower bound
        p2[x] = y
        fe += 1
    return (len(roots) - fe, fe)


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
