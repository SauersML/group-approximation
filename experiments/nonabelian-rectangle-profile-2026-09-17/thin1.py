"""thin non-abelian family: base N1 x N2 (N1 small), vertical slits of length ~ N2/2 with
non-commuting labels. Tracks exact rho vs best frame rounding as N2 grows.
usage: python3 thin1.py GROUP seed"""
import sys, random
from perm import *
G=sys.argv[1]; random.seed(int(sys.argv[2]))
els,mul=named_group(G); m=len(els)
worst=0
for N1 in [1,2,3]:
  for trial in range(4):
    nsl=random.choice([2,3]); spec=[(random.randrange(1,m),random.randrange(N1),random.random(),random.uniform(0.2,0.7)) for _ in range(nsl)]
    for N2 in [6,10,16,24,32]:
        T=Torus(N1,N2,0); beta=[0]*T.N; gamma=[0]*T.N
        for (h,x,y0,fr) in spec:
            y=int(y0*N2); L=max(1,int(fr*N2))
            for i in range(L):
                s=T.idx(x,y+i+1); beta[s]=mul[h,beta[s]]
        b,c=cover(T,mul,beta,gamma)
        if rkI(comm(b,c))==0: continue
        rho=profile(b,c)
        (ub,rb,rc,keep),f=best_rounding(b,c,2)
        worst=max(worst,ub/rho[0])
        print(G,N1,N2,spec if N2==6 else '', 'rho=%.3f'%rho[0],rho[1:],'ub=',ub,rb,rc,keep,f,'ub/rho=%.3f'%(ub/rho[0]),flush=True)
print('WORST',worst)
