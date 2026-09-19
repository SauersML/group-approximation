# Build the unique rank-7 gluing D of the three support cells and look for a closed path in D^1
# over the boundary of some lift of the d-cell (the only 2-cell a K(H,1) could still use).
from minrank import *
def build(blocks, lens):
    par = {}
    def fd(a):
        par.setdefault(a, a)
        while par[a] != a: a = par[a]
        return a
    ends = lambda k, i, o: (((k, i), (k, (i + 1) % lens[k])) if o > 0 else ((k, (i + 1) % lens[k]), (k, i)))
    for blk in blocks:
        o0, t0 = ends(blk[0][0], blk[0][1], blk[0][3])
        for (k, i, _, o) in blk[1:]:
            a, b = ends(k, i, o); par[fd(a)] = fd(o0); par[fd(b)] = fd(t0)
    return [(fd(ends(b[0][0], b[0][1], b[0][3])[0]), fd(ends(b[0][0], b[0][1], b[0][3])[1])) for b in blocks], fd
def rank7():
    K, occ, lens = setup(); keys = sorted(occ, key=str)
    opts = [[(keys[j], p) for p in zero_partitions(occ[keys[j]])] for j in range(len(keys))]
    out = []
    for ch in itertools.product(*opts):
        blocks = [b for _, p in ch for b in p]; img = [e for e, p in ch for b in p]
        if rank_of(blocks, lens)[0] <= 7: out.append((blocks, img))
    return K, lens, out
def dboundary(K, v):
    """Boundary of the d-cell lift at X_H vertex v, as (X_H edge, sign) list, or None if it leaves C_0."""
    try:
        te, fv = K.tedge(v); pe, w = K.walk(v, 'd'); te2, fw = K.tedge(w); pf, end = K.walk(fv, PHIB['d'])
    except ValueError: return None
    return [(te, 1)] + pf + [(te2, -1)] + [(x, -o) for x, o in reversed(pe)]
if __name__ == '__main__':
    K, lens, cands = rank7()
    print('rank-7 gluings:', len(cands))
    E0 = set(K.E)
    for blocks, img in cands:
        edges, fd = build(blocks, lens)
        verts = {x for e in edges for x in e}
        found = []
        for v in range(len(K.C.reps)):
            bd = dboundary(K, v)
            if bd is None or not all(e in E0 for e, _ in bd): continue
            # lift: start at any vertex of D, follow D-edges over each X_H edge with the right orientation
            for u in verts:
                paths = [(u, [])]
                for e, o in bd:
                    nxt = []
                    for cur, pth in paths:
                        for j, (a, b) in enumerate(edges):
                            if img[j] != e: continue
                            if o > 0 and a == cur: nxt.append((b, pth + [(j, 1)]))
                            if o < 0 and b == cur: nxt.append((a, pth + [(j, -1)]))
                    paths = nxt
                found += [(v, u, p) for end, p in paths if end == u]
        print('d-lifts inside C_0:', [v for v in range(len(K.C.reps)) if dboundary(K, v) and all(e in E0 for e, _ in dboundary(K, v))])
        print('closed lifts of a d-cell boundary in D^1:', len(found))
        for f in found: print(f)
