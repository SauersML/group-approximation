#!/usr/bin/env python3
"""Second-tier certified tests for LOT complexes.

- Barreto--Minian (arXiv:2308.07447) Thm 2.5 and Thm 2.18 (local indicability), and the maxima
  analogue (their Remark 2.3), obtained by inverting every generator: a homeomorphism of K_P that
  negates levels.  Local indicability with H_2 = 0 gives asphericity (their introduction, citing
  Howie).  For LOT presentations and label presentations, H_1 = Z, deficiency 1, H_2 = 0.
- Label presentations: Tietze elimination of every vertex that is not an edge label, along the tree
  from a label root.  Each elimination is a 3-deformation, so K(Gamma) ~ K(P_L), and every test of
  lot.py can be run on P_L instead.
"""
from collections import Counter
from lot import rel, test_itest, test_weight

def free_reduce(w):
    out = []
    for g in w:
        if out and out[-1][0] == g[0] and out[-1][1] == -g[1]: out.pop()
        else: out.append(g)
    return out

def cyc_reduce(w):
    w = free_reduce(w)
    while len(w) >= 2 and w[0][0] == w[-1][0] and w[0][1] == -w[-1][1]: w = w[1:-1]
    return w

def inv(w): return [(g, -e) for (g, e) in reversed(w)]

def ivalues(w):
    """Barreto--Minian Def. 2.14 with phi = 1 on every generator."""
    vals, s = [], 0
    for (g, e) in w:
        if e == 1: vals.append(s); s += 1
        else: s -= 1; vals.append(s)
    return vals

def minima(w):
    """Multiset m(r) (Def. 2.2 = Remark 2.16): letters attaining the minimum I-value."""
    v = ivalues(w); m = min(v)
    return Counter(g for x, (g, e) in zip(v, w) if x == m)

def signed_minima(w):
    v = ivalues(w); m = min(v)
    pos = Counter(g for x, (g, e) in zip(v, w) if x == m and e == 1)
    neg = Counter(g for x, (g, e) in zip(v, w) if x == m and e == -1)
    return pos, neg

def greedy_back(n, valid):
    """Ordering i_1..i_n where valid(i, earlier_set) holds; valid is monotone under shrinking
    the earlier set, so choosing any valid last element never loses solutions."""
    rem, back = list(range(n)), []
    while rem:
        pick = next((i for i in rem if valid(i, [j for j in rem if j != i])), None)
        if pick is None: return None
        rem.remove(pick); back.append(pick)
    return back[::-1]

def concat_order(sets):
    """Def. 2.4: each set has a multiplicity-one element outside the union of earlier sets."""
    def valid(i, earlier):
        u = set().union(*[set(sets[j]) for j in earlier]) if earlier else set()
        return any(c == 1 and g not in u for g, c in sets[i].items())
    return greedy_back(len(sets), valid)

def verify_concat(sets, order):
    seen = set()
    for i in order:
        if not any(c == 1 and g not in seen for g, c in sets[i].items()): return False
        seen |= set(sets[i])
    return sorted(order) == list(range(len(sets)))

def normalized(rels, flip):
    R = [cyc_reduce([(g, -e) for (g, e) in r] if flip else r) for r in rels]
    if any((not r) or sum(e for _, e in r) != 0 for r in R): return None
    return R

def test_bm25(ngen, rels):
    """Thm 2.5: deficiency 1, H_1 = Z, cyclically reduced relators of total exponent 0, minima
    multisets of all relators but one concatenable => locally indicable."""
    k = len(rels)
    if ngen != k + 1: return None
    for flip in (False, True):
        R = normalized(rels, flip)
        if R is None: continue
        sets = [minima(r) for r in R]
        for s in range(k):
            sub = [sets[j] for j in range(k) if j != s]
            o = concat_order(sub)
            if o is not None and verify_concat(sub, o):
                return {'thm': '2.5', 'maxima': flip, 'omit': s, 'order': o}
    return None

def test_bm218(ngen, rels):
    """Thm 2.18: H_1 free abelian of rank n - k, relators weakly concatenable (Def. 2.17)."""
    k = len(rels)
    if ngen - k != 1: return None
    for flip in (False, True):
        R = normalized(rels, flip)
        if R is None: continue
        info = [signed_minima(r) for r in R]
        def valid(i, earlier):
            u = set()
            for j in earlier: u |= set(info[j][0]) | set(info[j][1])
            pos, neg = info[i]
            return any(g not in u and pos[g] != neg[g] for g in set(pos) | set(neg))
        o = greedy_back(k, valid)
        if o is not None: return {'thm': '2.18', 'maxima': flip, 'order': o}
    return None

def label_presentations(n, E):
    """Yield (root, number of generators, relators) for every label root."""
    labels = sorted({l for (_, l, _) in E})
    idx = {v: r for r, v in enumerate(labels)}
    adj = {v: [] for v in range(n)}
    for (i, l, t) in E: adj[i].append((t, (i, l, t))); adj[t].append((i, (i, l, t)))
    for root in labels:
        W, parent, order = {root: [(idx[root], 1)]}, {}, [root]
        for v in order:
            for (w_, e) in adj[v]:
                if w_ not in parent and w_ != root:
                    parent[w_] = e; order.append(w_)
        rels = []
        for v in order[1:]:
            (i, l, t) = e = parent[v]
            p = t if i == v else i
            if v in idx:
                W[v] = [(idx[v], 1)]
            elif i == p:   # p l = l v  =>  v = l^-1 p l
                W[v] = free_reduce([(idx[l], -1)] + W[p] + [(idx[l], 1)])
            else:          # v l = l p  =>  v = l p l^-1
                W[v] = free_reduce([(idx[l], 1)] + W[p] + [(idx[l], -1)])
            r = free_reduce(W[i] + [(idx[l], 1)] + inv(W[t]) + [(idx[l], -1)])
            if v in idx: rels.append(cyc_reduce(r))
            elif r: raise AssertionError('elimination relator did not become trivial')
        yield root, len(labels), rels

def certify2(n, E):
    """Second-tier tests on the LOT presentation, then on every label presentation."""
    R = [rel(e) for e in E]
    for name, f in (('bm25', test_bm25), ('bm218', test_bm218)):
        c = f(n, R)
        if c: return name, c
    for root, g, RL in label_presentations(n, E):
        for name, f in (('L-bm25', test_bm25), ('L-bm218', test_bm218)):
            c = f(g, RL)
            if c: c.update(root=root, rels=RL); return name, c
        c = test_itest(g, None, rels=RL, vs=[[1] * g, [-1] * g])
        if c: c.update(root=root, rels=RL); return 'L-itest', c
    for root, g, RL in label_presentations(n, E):
        c = test_weight(g, None, rels=RL)
        if c: c.update(root=root, rels=RL); return 'L-weight', c
    return None, None
