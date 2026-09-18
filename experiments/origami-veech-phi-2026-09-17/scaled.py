"""Scaled origami O_m: each square of O subdivided into m x m small squares.
Computes the best exact affine lifts S_m, T_m (Schreier isomorphisms), the rank of every
relator of Z^2 x| SL_2(Z), and phi(L) = rank([B^L, C^L] - I)."""
import sys, time
from perm import *
from wms import B as B8, C as C8

def scale(b, c, m):
    n = len(b)
    I = lambda i,u,v: (i*m+u)*m+v
    Bm = [0]*(n*m*m); Cm = [0]*(n*m*m)
    for i in range(n):
        for u in range(m):
            for v in range(m):
                Bm[I(i,u,v)] = I(i,u+1,v) if u < m-1 else I(b[i],0,v)
                Cm[I(i,u,v)] = I(i,u,v+1) if v < m-1 else I(c[i],u,0)
    return tuple(Bm), tuple(Cm)

def best_tuple(b, c):
    Ts = list(isos((b,c),(b,mul(b,c))))
    Ss = list(isos((b,c),(c,inv(b))))
    best = None
    for s in Ss:
        for t in Ts:
            tot = {k:perm_rank_defect(v) for k,v in relators(b,c,s,t).items()}
            if best is None or max(tot.values()) < max(best[0].values()):
                best = (tot,s,t)
    return best, len(Ss), len(Ts)

if __name__ == "__main__":
    for m in [int(a) for a in sys.argv[1:]]:
        t0 = time.time()
        b, c = scale(B8, C8, m)
        d = len(b)
        (tot,s,t), ns, nt = best_tuple(b, c)
        phis = {L: perm_rank_defect(comm(power(b,L),power(c,L))) for L in sorted({1,2,m//4 or 1,m//2 or 1,m})}
        print("m=%d d=%d  #S-lifts=%d #T-lifts=%d  relator ranks %s  phi %s  (%.1fs)" % (m,d,ns,nt,tot,phis,time.time()-t0))
        sys.stdout.flush()
