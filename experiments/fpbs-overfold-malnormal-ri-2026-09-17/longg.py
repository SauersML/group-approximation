"""Long-g search for the top case of k = 1 relative inertia (swarm-0917-w19-w19-fp-follow).

B <= F(a,b) of rank 2, rho : B -> G onto a non-cyclic group, X = ker rho.
Search all reduced g with |g| <= LMAX for <X, g> >= B.  Each hit is a
violation of (RI_B) at k = 1, since rk(B : X) = d(G) = 2 > 1 = rk(<X,g> : X).

usage: python3 longg.py BSPEC GROUP LMAX [MAXRHO]
  BSPEC = L1 | L2 | words w1,w2 (over a,A,b,B)
"""
import sys
from itertools import product
from stall import red, inv, fold_graph, member, rank, L
from maln import malnormal
from ri1 import GROUPS, closure, pmul

INVL = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def kernel_words(Bg, imgs, n):
    """Schreier generators (as words in F) of ker(rho), rho(Bg[i]) = imgs[i]."""
    e = tuple(range(n))
    path = {e: []}
    order = [e]
    for x in order:
        for i, gi in enumerate(imgs):
            y = pmul(x, gi)
            if y not in path:
                path[y] = path[x] + [Bg[i]]
                order.append(y)
    words = []
    for x in order:
        for i, gi in enumerate(imgs):
            y = pmul(x, gi)
            w = red(''.join(path[x]) + Bg[i] + inv(''.join(path[y])))
            if w:
                words.append(w)
    return words


def canon(G):
    """Canonical key of a folded based graph (BFS from base, letter order aAbB)."""
    adj, base = G
    idx = {base: 0}
    order = [base]
    for v in order:
        for x in 'aAbB':
            if x in adj[v] and adj[v][x] not in idx:
                idx[adj[v][x]] = len(idx)
                order.append(adj[v][x])
    return tuple(tuple(idx[adj[v][x]] if x in adj[v] else -1 for x in 'aAbB') for v in order)


def words_upto(lmax):
    frontier = ['']
    for l in range(1, lmax + 1):
        nf = []
        for w in frontier:
            for x in 'aAbB':
                if w and w[-1] == INVL[x]:
                    continue
                nf.append(w + x)
        frontier = nf
        for w in frontier:
            yield w


def main():
    spec, gname, lmax = sys.argv[1], sys.argv[2], int(sys.argv[3])
    maxrho = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 9
    Bg = {'L1': L(1), 'L2': L(2)}.get(spec) or spec.split(',')
    BG = fold_graph(Bg)
    print('B =', Bg, 'rank', rank(BG), 'malnormal', malnormal(BG), flush=True)
    els, n = GROUPS[gname]
    seen = set()
    nrho = 0
    hits = 0
    # Only rho that do not extend to an onto sigma : F -> G can give hits
    # (Proposition N of the artifact), and only for B = L_1 is the extension
    # test implemented here (restriction map (A,B) -> (A, B A B^-2)).
    ext = set()
    if spec == 'L1':
        from extend import word
        for A in els:
            for Bx in els:
                if len(closure([A, Bx], n)) == len(els):
                    ext.add((A, word(A, Bx)))
    for imgs in product(els, repeat=2):
        if len(closure(list(imgs), n)) != len(els):
            continue
        if imgs in ext:
            continue
        Xw = kernel_words(Bg, imgs, n)
        XG = fold_graph(Xw)
        key = canon(XG)
        if key in seen:
            continue
        seen.add(key)
        nrho += 1
        if nrho > maxrho:
            break
        from stall import basis
        Xb = basis(XG)[1]
        nw = 0
        for g in words_upto(lmax):
            if member(BG, g):
                continue
            nw += 1
            JG = fold_graph(Xb + [g])
            if all(member(JG, w) for w in Bg):
                hits += 1
                print('HIT rho=%s g=%s rkJ=%d' % (imgs, g, rank(JG)), flush=True)
        print('rho', nrho, imgs, 'rkX', len(Xb), 'words tested', nw, 'hits so far', hits, flush=True)
    print('DONE', spec, gname, lmax, 'distinct kernels', nrho, 'hits', hits)


if __name__ == '__main__':
    main()
