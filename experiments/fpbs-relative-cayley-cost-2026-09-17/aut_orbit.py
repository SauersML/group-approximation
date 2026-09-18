"""Is the pair (F_2, H) in the Aut(F_2)-orbit of (F_2, K), K = <c, dcDD>?

Breadth-first search over images of H under elementary Nielsen/Whitehead
automorphisms, keeping only images whose Stallings core has at most
`bound` vertices; compares against the same search from K using a canonical
form of the based core graph up to basepoint change (conjugacy) and letter
symmetries (automorphisms permuting/inverting letters).
"""
import sys
from stallings import fold, core, INV

AUTS = []
for x, y in (('c', 'd'), ('d', 'c')):
    X, Y = INV[x], INV[y]
    # x -> x y, x -> y x, x -> y x Y  (and with inverses of y)
    for yy in (y, Y):
        AUTS.append({x: x + yy})
        AUTS.append({x: yy + x})
        AUTS.append({x: yy + x + INV[yy]})


def apply(aut, w):
    out = []
    for l in w:
        if l in aut:
            out.append(aut[l])
        elif INV[l] in aut:
            out.append(''.join(INV[m] for m in reversed(aut[INV[l]])))
        else:
            out.append(l)
    return reduce(''.join(out))


def reduce(w):
    st = []
    for l in w:
        if st and st[-1] == INV[l]:
            st.pop()
        else:
            st.append(l)
    return ''.join(st)


SYMS = []
for pc in ('c', 'C', 'd', 'D'):
    for pd in ('c', 'C', 'd', 'D'):
        if pc.lower() == pd.lower():
            continue
        SYMS.append({'c': pc, 'C': INV[pc], 'd': pd, 'D': INV[pd]})


def canon(gens):
    """Canonical string of core graph up to basepoint and letter symmetry."""
    G, b = fold(gens)
    A = sorted(core(G, b))
    best = None
    for sym in SYMS:
        for root in A:
            # BFS relabel
            lab = {root: 0}
            order = [root]
            i = 0
            while i < len(order):
                v = order[i]
                i += 1
                for l in ('c', 'C', 'd', 'D'):
                    # symmetric letter l' such that sym[l'] = l
                    src = [k for k in sym if sym[k] == l][0]
                    if src in G.adj[v] and G.adj[v][src] in A:
                        w = G.adj[v][src]
                        if w not in lab:
                            lab[w] = len(order)
                            order.append(w)
            if len(lab) != len(A):
                continue
            edges = []
            for v in A:
                for src in ('c', 'd', 'C', 'D'):
                    if src in G.adj[v] and G.adj[v][src] in A:
                        l = sym[src]
                        if l in ('c', 'd'):
                            edges.append((lab[v], l, lab[G.adj[v][src]]))
                        else:
                            edges.append((lab[G.adj[v][src]], INV[l], lab[v]))
            s = str(sorted(set(edges)))
            if best is None or s < best:
                best = s
    return best, len(A)


def orbit(gens, bound, limit=200000):
    start = tuple(gens)
    seen = {canon(list(start))[0]: start}
    frontier = [start]
    while frontier and len(seen) < limit:
        nf = []
        for g in frontier:
            for a in AUTS:
                img = [apply(a, w) for w in g]
                key, size = canon(img)
                if size <= bound and key not in seen:
                    seen[key] = tuple(img)
                    nf.append(tuple(img))
        frontier = nf
    return seen


if __name__ == '__main__':
    bound = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    K = ['c', 'dcDD']
    Kc = orbit(K, bound)
    print('K orbit core-types with size <=', bound, ':', len(Kc),
          'min size', min(canon(list(g))[1] for g in Kc.values()))
    for name, H in (('H_c(cdcDcd)', ['c', 'dcDcd']), ('H_d(cdcDcd)', ['d', 'cdcDc'])):
        Ho = orbit(H, bound)
        inter = set(Ho) & set(Kc)
        print(name, 'orbit types', len(Ho), 'min size',
              min(canon(list(g))[1] for g in Ho.values()),
              'meets K-orbit:', bool(inter))
        if inter:
            k = next(iter(inter))
            print('  common representative', Ho[k], Kc[k])
