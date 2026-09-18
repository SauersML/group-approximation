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

Additions of this file (fpbs-tree-projected-pollard-slot-second-moment; terms are now
m-specific, strategies compared at M_REF = m):
  POL    -- Pollard pair counts: a determined y = e1 x1 + e2 x2 + (revealed) confines the
            pair (x1, x2) to at most P_plain(m) = min_t [m t + (m-t)^2] values, or
            P_neq(m) = min_t [m t + (m-t)(m-t-1)] when x1 != x2, same letter, e1 = -e2.
  NONAP  -- non-AP collision: y = x + gam, same letter, gam provably nonzero gives
            |D cap (D - gam)| <= m - 2 (equality m - 1 forces an AP; rigid sets are not APs).
  PW     -- (experimental, not certified) generic source row made affine in the
            autocorrelation parameters R_kap(h + j c); see runpw.py.
  WAUG   -- (experimental, not certified) S-weighted generic landing mass W_AGG.

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


# ---------------------------------------------------------------- Pollard pair counts
POL = False       # sumset refinement (see the -proof node, section "Pollard pairs")
M_REF = None      # the multiplicity m at which strategies are compared (terms are m-specific)


def P_plain(m):
    """max over m-sets A, B, S of Z and nonzero rationals a1, a2 of
    #{(x1, x2) in A x B : a1 x1 + a2 x2 in S}  <=  min_t [ m t + (m - t)^2 ]   (Pollard)."""
    return min(m * t + (m - t) ** 2 for t in range(m + 1))


def P_neq_eff(m):
    """Pollard bound for a same-letter pair x1 != x2 confined to x1 - x2 in a set of size m,
    sharpened by the chain deficiency: sum over the m admissible differences s != 0 of
    r_D(s) <= m (m - KAP)  (flag PNX)."""
    if PNX and NONAP:
        return min(P_neq(m), m * (m - KAP))
    return P_neq(m)


PNX = True


def P_neq(m):
    """#{(x1, x2) in A x A : x1 != x2, a (x1 - x2) in S} <= min_t [ m t + (m-t)(m-t-1) ]."""
    return min(m * t + (m - t) * (m - t - 1) for t in range(m + 1))


def desc_value(d, m):
    if len(d) == 2:
        c, f = d
        return F(m) ** c * F(m - 1) ** f
    if len(d) == 4:
        c, f, a, b = d
        return F(m) ** c * F(m - 1) ** f * F(P_plain(m)) ** a * F(P_neq(m)) ** b
    c, f, a, b, g2 = d
    return F(m) ** c * F(m - 1) ** f * F(P_plain(m)) ** a * F(P_neq_eff(m)) ** b * F(m - KAP) ** g2


KAP = 2           # chain deficiency: |D cap (D+g)| <= m - KAP for g != 0 (KAP = 2: rigid => not an AP)
NONAP = False     # non-AP gain: |D cap (D + g)| <= m - 2 for g != 0 (rigid => D not an AP)


def nonap_level(expr_y, dy, dom, K, generic):
    """2 if y = x + gam, x a single free variable of the same letter as y and gam provably
    nonzero (then #{x in D : x + gam in D} = |D cap (D - gam)| <= m - 2 unless D is an
    arithmetic progression, which rigidity excludes); else 1."""
    xs = [k for k in expr_y if k not in ('h', 'c')]
    if len(xs) != 1:
        return 1
    x = xs[0]
    gam = {k: v for k, v in expr_y.items() if k in ('h', 'c')}
    if expr_y[x] == 1 and dom[x] == dy and _nonzero(gam, K, generic):
        return 2
    return 1


def _forest_rig(free, ineqs, ex, dom, K, generic):
    """(comps, fedges+gains) of the RIGID forest bound on the free set `free`, using only the
    determined expressions in ex whose single free variable lies in `free`."""
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
    g = 0
    g2 = 0
    pars = []
    if RIGID:
        best = {}      # tree -> best gain level (1: root m-1, 2: root m-2)
        for d, e in ex.items():
            x = restricted(e, dom[d], dom, K, generic)
            if x is not None and x in parent:
                lv = nonap_level(e, dom[d], dom, K, generic) if NONAP else 1
                t = find(x)
                best[t] = max(best.get(t, 0), lv)
        if PW and generic:
            for d, e in ex.items():
                x = restricted(e, dom[d], dom, K, generic)
                if x is not None and x in parent:
                    lv = nonap_level(e, dom[d], dom, K, generic) if NONAP else 1
                    t = find(x)
                    pr = param_of(e, dom[d], x, dom, K)
                    if pr is not None and lv == best[t] and pr[1] == (M_REF - 1 if lv == 1 else M_REF - KAP):
                        pars.append((lv, pr[0]))
        g = sum(1 for v in best.values() if v == 1)
        g2 = sum(1 for v in best.values() if v == 2)
    if PW and generic:
        return (len(free) - fe - g - g2, fe + g, g2), pars
    if NONAP:
        return (len(free) - fe - g - g2, fe + g, g2)
    return (len(free) - fe - g, fe + g)


PW = False        # pointwise-in-h parametrisation of the generic source row


def param_of(expr_y, dy, x, dom, K):
    """y = a x + gam with a = +-1 and gam = beta h + alpha c, beta = +-1.  Then
    #{x in D_x : a x + gam in D_y} = R_kappa(h + j c), where for kappa = ((d1, s1), (d2, s2))
    R_kappa(g) = #{(u, w) in D_d1 x D_d2 : s1 u + s2 w = g}, with s_y = beta, s_x = -beta a,
    j = beta alpha.  Returns ((kappa, j), cap) with cap an upper bound for R_kappa(h + j c)
    valid for every rigid decoration, every letter context and every generic h
    (h + j c != 0 is guaranteed only for |j| <= K), or None."""
    m = M_REF
    a = expr_y[x]
    be = expr_y.get('h', F(0))
    al = expr_y.get('c', F(0))
    if a not in (1, -1) or be not in (1, -1):
        return None
    j = be * al
    if j.denominator != 1:
        return None
    j = int(j)
    kap = tuple(sorted([(dy, int(be)), (dom[x], int(-be * a))]))
    return ((kap, j), param_cap((kap, j), m, K))


def param_cap(key, m, K):
    """Upper bound for R_kappa(h + j c), h generic (see param_of)."""
    kap, j = key
    (d1, s1), (d2, s2) = kap
    nz = abs(j) <= K
    if d1 == d2 and s1 == -s2:      # autocorrelation of one set
        cap = ((m - KAP) if NONAP else (m - 1)) if nz else m
    elif d1 == d2:                  # D vs -D: never translates
        cap = m - 1
    elif s1 == s2:                  # distinct labels, possibly inverse directions
        cap = (m - 1) if nz else m
    else:                           # distinct directions: never translates
        cap = m - 1
    return cap


def count_bound_pol(rows, vars_, ineqs, dom, K, generic, key=None):
    """Upper bound for the number of solutions, as count_bound_rig, and in addition:
    a determined variable y whose expression contains two free variables x1, x2 (nonzero
    coefficients) confines the pair (x1, x2), for fixed values of its other free variables,
    to at most P_plain(m) values (Pollard), or P_neq(m) if x1, x2 have the same letter,
    opposite coefficients and x1 != x2 is an ensemble inequality.  Pairs are revealed after
    the remaining free variables, in an order in which every y only involves revealed
    variables.  Returns the descriptor (comps, fedges, n_plain, n_neq) minimising the value
    at m = M_REF."""
    if key is not None and key in _cb_memo:
        return _cb_memo[key]
    m = M_REF
    rows = [r for r in rows if any(k not in ('h', 'c') for k in r)]
    k = len(vars_)
    r = rank_cols(rows, vars_)
    best, bestv = None, None
    ineqset = {frozenset(q) for q in ineqs}
    for free in combinations(vars_, k - r):
        det = [a for a in vars_ if a not in free]
        if det and rank_cols(rows, det) != r:
            continue
        ex = _express(rows, det) if det else {}
        if ex is None:
            continue
        # pair candidates: (y, frozenset{x1,x2}, support, kind)
        pc = []
        for y, e in ex.items():
            sup = [a for a in e if a not in ('h', 'c')]
            if len(sup) < 2:
                continue
            for x1, x2 in combinations(sup, 2):
                neq = (dom[x1] == dom[x2] and e[x1] == -e[x2] and frozenset((x1, x2)) in ineqset)
                pc.append((y, frozenset((x1, x2)), frozenset(sup), 1 if neq else 0))
        # enumerate sets of candidates with distinct y and disjoint pairs, orderable
        opts = [()]
        def rec(i, chosen, usedy, usedx):
            if i == len(pc):
                return
            for j in range(i, len(pc)):
                y, pr, sup, kd = pc[j]
                if y in usedy or (pr & usedx):
                    continue
                ch = chosen + (pc[j],)
                opts.append(ch)
                rec(j + 1, ch, usedy | {y}, usedx | pr)
        rec(0, (), frozenset(), frozenset())
        for ch in opts:
            pairvars = set().union(*[c[1] for c in ch]) if ch else set()
            rest = [a for a in free if a not in pairvars]
            # order check: repeatedly reveal a pair whose support is covered
            known = set(rest)
            left = list(ch)
            okord = True
            while left:
                nxt = next((c for c in left if c[2] <= known | c[1]), None)
                if nxt is None:
                    okord = False
                    break
                known |= nxt[1]
                left.remove(nxt)
            if not okord:
                continue
            cf = _forest_rig(rest, ineqs, {d: e for d, e in ex.items() if all(c[0] != d for c in ch)}, dom, K, generic)
            pars = []
            if PW and generic:
                cf, pars = cf
            npl = sum(1 for c in ch if c[3] == 0)
            nnq = sum(1 for c in ch if c[3] == 1)
            d = (cf[0], cf[1], npl, nnq) + ((cf[2],) if NONAP else ())
            v = desc_value(d, m)
            if PW and generic:
                par = None
                if pars:
                    lv, key0 = sorted(pars)[0]
                    dd = list(d)
                    if lv == 1:
                        dd[1] -= 1
                    else:
                        dd[4] -= 1
                    par = (key0, tuple(dd))
                if bestv is None or v < bestv or (v == bestv and par is not None and best[1] is None):
                    best, bestv = (d, par), v
                continue
            if bestv is None or v < bestv:
                best, bestv = d, v
    if best is None:
        best = (k - r, 0, 0, 0) + ((0,) if NONAP else ())
        if PW and generic:
            best = (best, None)
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
                                    assert cl != 'G'
                                    if POL:
                                        ub = count_bound_pol([r for _, r in rr], vars_, ineqs, dom, K, cl == 'G')
                                        assert desc_value(ub, M_REF) >= desc_value(lb, M_REF), 'UB < exact count'
                                    for nq, mult in nqs.items():
                                        kk = (si, NZ, ne, nq) + ((lb[0], lb[1], 0, 0) + ((0,) if NONAP else ()) if POL else (lb[0], lb[1])) + ((None,) if PW else ())
                                        agg[kk] = agg.get(kk, 0) - mult
                    if WAUG and not bad:
                        # S-weighted generic landing mass: sum over solutions with h' generic of
                        # R_kap(h') = #{(u, w) in D_kap^2 : u - w = h'} (u != w since h' != 0)
                        for kap in LETTERS:
                            ra, _ = rref_add(rr, add(add(var('Wu'), neg(var('Ww'))), neg(hp)), order + ['Wu', 'Ww'])
                            if is_forced(ra):
                                continue
                            v2 = vars_ + ['Wu', 'Ww']
                            dm2 = dict(dom); dm2['Wu'] = dm2['Ww'] = kap
                            iq2 = ineqs + [('Wu', 'Ww')]
                            rwa = [r for _, r in ra]
                            if POL:
                                dW = count_bound_pol(rwa, v2, iq2, dm2, K, cl == 'G',
                                                     key=('polW', RIGID, NONAP, PW, M_REF, rref_key(ra), tuple(v2), tuple(iq2),
                                                          tuple(sorted(dm2.items())), K, cl == 'G'))
                                if PW and cl == 'G':
                                    dW = dW[0]
                            else:
                                dW = count_bound(rwa, v2, iq2, key=('W', rref_key(ra), tuple(v2), tuple(iq2)))
                            for nq, mult in nqs.items():
                                kk = (si, kap, ne, nq) + tuple(dW)
                                W_AGG[kk] = W_AGG.get(kk, 0) + mult
                    for ti, r2 in targets:
                        rws = [r for _, r in r2]
                        if POL:
                            d = count_bound_pol(rws, vars_, ineqs, dom, K, cl == 'G',
                                                key=('pol', RIGID, NONAP, PW, M_REF, rref_key(r2), tuple(vars_), tuple(ineqs),
                                                     tuple(sorted(dom.items())), K, cl == 'G'))
                        elif RIGID:
                            d = count_bound_rig(rws, vars_, ineqs, dom, K, cl == 'G',
                                                key=('rig', RIGID2, rref_key(r2), tuple(vars_), tuple(ineqs),
                                                     tuple(sorted(dom.items())), K, cl == 'G'))
                        else:
                            d = count_bound(rws, vars_, ineqs,
                                            key=(rref_key(r2), tuple(vars_), tuple(ineqs)))
                        par = None
                        if PW and cl == 'G':
                            d, par = d
                            if par is not None:
                                par, d = par
                        if DEBUG is not None:
                            DEBUG.append((si, ti, s1, s2, rws, dict(nqs), tuple(d), ne, par))
                        for nq, mult in nqs.items():
                            kk = (si, ti, ne, nq) + tuple(d) + ((par,) if PW else ())
                            agg[kk] = agg.get(kk, 0) + mult
                    if PW and cl == 'G' and not rr and s1[1] == () and s2[1] == () and s1[2] == 0 and s2[2] == 0:
                        # Q = {} for two excursion-free slots: the pairs landing at h' = k c are
                        # EXACTLY #{(ps, Ps) in D_t^2 : ps - Ps = h + (V2 - V1 - k) c}
                        # = R_((t,-1),(t,1))(h + j c); subtract them from the generic target
                        # (all k) and from NZ (k = 0).  Only exact pair ensembles: one vertical
                        # edge at most per path, so no internal coincidence exists.
                        assert nqs == {0: 1} and len(vars_) == 2
                        for k in specials:
                            j = s2[0] - s1[0] - k
                            kap = ((('t', -1), ('t', 1)), j)
                            z = (0, 0, 0, 0, 0)
                            for tg in ([ncl - 1] + ([NZ] if k == 0 else [])):
                                kk = (si, tg, ne, 0) + z + (kap,)
                                agg[kk] = agg.get(kk, 0) - 1
        if verbose:
            print('class', cl, 'done; aggregated terms', len(agg), flush=True)
    if PW:
        return [(k[0], k[1], v, k[2], k[3], tuple(k[4:-1]), k[-1]) for k, v in agg.items() if v], ncl
    return [(k[0], k[1], v, k[2], k[3], tuple(k[4:])) for k, v in agg.items()], ncl


NZREF = False
DEBUG = None
WAUG = False      # also build the S-weighted generic landing terms (W_AGG)
W_AGG = {}


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
        T[st][tg] += mult * p ** ne * (x - 1) ** nq * desc_value(d, m)
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
