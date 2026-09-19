# Lower bound for the map version of (T0) on the split-basis rose: every 2-cell-injective map K -> (M_f)_H
# from a K(H,1) contains the three support cells, glued so that the canonical cycle has zero boundary in K.
# For each partition of the edge occurrences into zero-sum blocks (the K-edges over each edge of X_H),
# compute the rank of the forced quotient graph of the three cell boundaries.
import itertools
from cplx import *
SUPPORT = [(1, 'a', 'ABCC'), (2, 'b', ''), (2, 'c', 'D')]
def setup():
    K = Cplx(); occ = {}; lens = []
    for k, (n, l, v) in enumerate(SUPPORT):
        bd = K.add_cell(l, v); lens.append(len(bd))
        for i, (e, o) in enumerate(bd): occ.setdefault(e, []).append((k, i, n * o, o))
    return K, occ, lens
def zero_partitions(items):
    """All set partitions of items into blocks with zero coefficient sum."""
    if not items: yield []; return
    first, rest = items[0], items[1:]
    for r in range(len(rest) + 1):
        for comb in itertools.combinations(rest, r):
            blk = (first,) + comb
            if sum(x[2] for x in blk) == 0:
                left = [x for x in rest if x not in comb]
                for p in zero_partitions(left): yield [blk] + p
def rank_of(blocks, lens):
    par = {}
    def fd(a):
        par.setdefault(a, a)
        while par[a] != a: par[a] = par[par[a]]; a = par[a]
        return a
    def un(a, b): par[fd(a)] = fd(b)
    corners = [(k, i) for k, L in enumerate(lens) for i in range(L)]
    for c in corners: fd(c)
    ends = lambda k, i, o: (((k, i), (k, (i + 1) % lens[k])) if o > 0 else ((k, (i + 1) % lens[k]), (k, i)))
    for blk in blocks:
        o0, t0 = ends(blk[0][0], blk[0][1], blk[0][3])
        for (k, i, _, o) in blk[1:]:
            a, b = ends(k, i, o); un(a, o0); un(b, t0)
    V = {fd(c) for c in corners}
    # components: corners linked by blocks (every block joins its two ends)
    comp = {v: v for v in V}
    def cf(a):
        while comp[a] != a: a = comp[a]
        return a
    for blk in blocks:
        a, b = ends(blk[0][0], blk[0][1], blk[0][3]); comp[cf(fd(a))] = cf(fd(b))
    C = len({cf(v) for v in V})
    return len(blocks) - len(V) + C, len(blocks), len(V), C
if __name__ == '__main__':
    K, occ, lens = setup()
    opts = [list(zero_partitions(occ[e])) for e in sorted(occ, key=str)]
    print('cell lengths', lens, 'edges of X_H used', len(occ), 'choices', [len(o) for o in opts])
    res = []
    for ch in itertools.product(*opts):
        blocks = [b for p in ch for b in p]
        res.append(rank_of(blocks, lens))
    res.sort()
    print('min (rank, E, V, components):', res[0], ' max:', res[-1], ' #partitions:', len(res))
    print('rank bound from chi(K) = -2 with at most 4 two-cells: rank(K^1) <= 7')
