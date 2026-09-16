"""Sanity check: reduced GF(2) homology of the descending coface link VR_t(W_0) in Z^2 (l^1), t=6, r_t=5,
for sets S of diameter 6 in case 2. W_0 = points within t of all of S, minus S. Expected: all zero."""
import sys
import local_lp_search as L
t = 6
def d(p, q): return abs(p[0]-q[0]) + abs(p[1]-q[1])
for S in [((0,0),(6,0)), ((0,0),(3,3)), ((0,0),(6,0),(3,3)), ((0,0),(4,2),(1,5))]:
    if max(d(a,b) for a in S for b in S) != t:
        print('skip', S); continue
    pts = [(a,b) for a in range(-7,14) for b in range(-7,14)]
    W = [p for p in pts if p not in S and all(d(p,s) <= t for s in S)]
    U = [p for p in W if all(d(p,s) <= 5 for s in S)]
    caseone = any(all(d(y,s) <= 5 for s in S) for y in S)
    n = len(W)
    adj = [sum(1 << j for j in range(n) if j != i and d(W[i], W[j]) <= t) for i in range(n)]
    cl = L.cliques(adj, n)
    print(S, 'case1' if caseone else 'case2', '|W0|', n, '|Y(S)|', len(U), '#simplices', len(cl) - 1,
          'reduced betti', L.reduced_betti(cl, n), flush=True)
