"""Cross-slit pair X(l,L): base Z/L (vertical), fibre F = Z/l x {0,1}.
b(j,(i,e)) = (j, beta_j(i,e)), beta_j = rotation i->i+1 on both sheets, except beta_{j0} = rotation
followed by the swap of (0,0),(0,1) (one b-cycle of length 2l).  c(j,(i,e)) = (j+1, gamma_j(i,e)),
gamma_j = id except gamma_{j1} = swap of (0,0),(0,1) (one c-cycle of length 2L).
dist <= 1 (undo both swaps), so rho <= 2.  Prints exact rho and the best one-sided (centralizer)
rounding over all GL2(Z) frames with entries <= M.   usage: python3 crossslit.py M"""
import sys
import numpy as np
from perm import *
M=int(sys.argv[1])
def pair(l,L,j0=0,j1=None):
    if j1 is None: j1=L//2
    n=2*l*L; idx=lambda j,i,e: (j%L)*2*l+2*(i%l)+e
    b=np.empty(n,int); c=np.empty(n,int); b0=np.empty(n,int); c0=np.empty(n,int)
    for j in range(L):
        for i in range(l):
            for e in (0,1):
                t=(i+1,e); b0[idx(j,i,e)]=idx(j,*t)
                if j==j0 and (i+1)%l==0: t=(0,1-e)
                b[idx(j,i,e)]=idx(j,*t)
                s=(i,e); c0[idx(j,i,e)]=idx(j+1,*s)
                if j==j1 and i==0: s=(0,1-e)
                c[idx(j,i,e)]=idx(j+1,*s)
    assert np.array_equal(comp(b0,c0),comp(c0,b0))
    return b,c,b0,c0
for (l,L) in [(3,3),(4,4),(6,6),(8,8),(10,10),(12,12),(16,16),(6,20),(20,6)]:
    b,c,b0,c0=pair(l,L)
    d=max(rk(b,b0),rk(c,c0))
    rho=profile(b,c)
    (ub,rb,rc,keep),f=best_rounding(b,c,M)
    print(l,L,'n=',2*l*L,'dist<=',d,'rho=%.3f'%rho[0],rho[1:],'best one-sided frame cost',ub,(rb,rc,keep),f,flush=True)
