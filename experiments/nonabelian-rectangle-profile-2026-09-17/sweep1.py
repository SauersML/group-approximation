"""random slit covers with non-abelian fibre: exact profile vs best frame rounding.
usage: python3 sweep1.py GROUP seed ncases"""
import sys, random
from perm import *
G=sys.argv[1]; random.seed(int(sys.argv[2])); ncase=int(sys.argv[3])
els,mul=named_group(G); m=len(els)
worst=0
for it in range(ncase):
    N1=random.choice([1,2,3,4,5,6]); N2=random.choice([2,3,4,6,8,10,12]); C=random.randrange(N1)
    T=Torus(N1,N2,C); beta=[0]*T.N; gamma=[0]*T.N
    nsl=random.choice([1,2,3])
    desc=[]
    for _ in range(nsl):
        h=random.randrange(1,m); x=random.randrange(N1); y=random.randrange(N2); L=random.randrange(1,max(N1,N2)+2)
        vert=random.random()<0.5
        for i in range(L):
            if vert:  # vertical slit: change beta along column -> horizontal gluing
                s=T.idx(x,y+i+1); beta[s]=mul[h,beta[s]]
            else:
                s=T.idx(x+i+1,y); gamma[s]=mul[h,gamma[s]]
        desc.append((h,x,y,L,'v' if vert else 'h'))
    b,c=cover(T,mul,beta,gamma)
    if rkI(comm(b,c))==0: continue
    rho=profile(b,c)
    (ub,rb,rc,keep),f=best_rounding(b,c,2)
    ratio=ub/rho[0]
    worst=max(worst,ratio)
    print(G,N1,N2,C,desc,'rho=%.3f'%rho[0],rho[1:],'ub=',ub,rb,rc,keep,f,'ub/rho=%.3f'%ratio,flush=True)
print('WORST',worst)
