"""Finite covers of folded graphs: kernel of a hom <G> -> Sym(n) on a basis."""
from stall import basis, INV, prune


def kernel_graph(G, perms):
    """perms[i] = permutation (tuple) for basis generator i of <G>.
    Returns the folded graph of ker(<G> -> Sym(n)) (the base component of the
    cover of G, pruned) -- as a subgroup of F(a,b)."""
    adj, base = G
    _, _, eidx = basis(G)
    n = len(perms[0])
    ident = tuple(range(n))
    lab = {}
    for v in adj:
        for x, w in adj[v].items():
            if x in 'ab':
                p = perms[eidx[(v, x)]] if (v, x) in eidx else ident
                lab[(v, x)] = p
    idx = {(base, 0): 0}
    order = [(base, 0)]
    nadj = {0: {}}
    for (v, s) in order:
        i = idx[(v, s)]
        for x, w in adj[v].items():
            if x in 'ab':
                t = (w, lab[(v, x)][s])
            else:
                p = lab[(w, INV[x])]
                t = (w, p.index(s))
            if t not in idx:
                idx[t] = len(idx)
                order.append(t)
                nadj[idx[t]] = {}
            nadj[i][x] = idx[t]
    return prune((nadj, 0))
