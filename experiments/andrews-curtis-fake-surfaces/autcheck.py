#!/usr/bin/env python3
# autcheck.py -- brute-force count of half-edge automorphisms (bijections of half-edges that preserve the vertex
# partition and the edge pairing) for every connected 4-regular multigraph of complexity t <= 4, independent of
# the backtracking automorphism routine in fsenum.cpp.  Prints graph index and count.
import itertools, sys, collections
import fsac
for t in range(1, int(sys.argv[1]) + 1):
    for gi, A in enumerate(fsac.load_graphs(t), 1):
        S = fsac.Surface(A); H = len(S.vert); byv = collections.defaultdict(list)
        for h in range(H): byv[S.vert[h]].append(h)
        count = 0
        for p in itertools.permutations(range(t)):
            if any(A[p[u]][p[w]] != A[u][w] for u in range(t) for w in range(t)): continue
            for bij in itertools.product(*[list(itertools.permutations(byv[p[v]])) for v in range(t)]):
                phi = [0]*H
                for v in range(t):
                    for h, img in zip(byv[v], bij[v]): phi[h] = img
                if all(phi[h ^ 1] == phi[h] ^ 1 for h in range(0, H, 2)): count += 1
        print(f"t={t} graph {gi} brute|Aut|={count}")
