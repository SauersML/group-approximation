# Vectorised version of rho2.py: Schur test with weights c(state,tau) u^(-beta) for walks with no cycle of length <= ell.
import sys, math
from fractions import Fraction
import numpy as np
ell=int(sys.argv[1]); u=float(Fraction(sys.argv[2])) if len(sys.argv)>2 else math.sqrt(3); iters=int(sys.argv[3]) if len(sys.argv)>3 else 400
Da=(0,1,3); Db=(0,1,4)
gens=[(1,d) for d in Da]+[(-1,-d) for d in Da]+[(2,d) for d in Db]+[(-2,-d) for d in Db]+[(0,1),(0,-1)]
G=len(gens)
def mul(w,g):
    word,h=w; l,d=g
    if l==0: return (word,h+d)
    if word and word[-1]==-l: return (word[:-1],h+d)
    return (word+(l,),h+d)
E=((),0)
def ok_ext(steps):
    # new vertex (after all steps) differs from vertex before the last j steps, j=1..len
    x=E
    for g in reversed(steps):
        # left-multiplying by g: product g*x ; compute product of suffix
        pass
    for j in range(2,len(steps)+1):
        x=E
        for g in steps[-j:]: x=mul(x,g)
        if x==E: return False
    return True
m=ell-1
states=[()]
for k in range(m):
    states=[s+(gi,) for s in states for gi in range(G) if ok_ext([gens[i] for i in s+(gi,)])]
idx={s:i for i,s in enumerate(states)}
N=len(states)
src=[];dst=[];gl=[]
for s in states:
    for gi in range(G):
        full=s+(gi,)
        if len(full)>=2 and not ok_ext([gens[i] for i in full]): continue
        ns=full[-m:] if m>0 else ()
        src.append(idx[s]); dst.append(idx[ns]); gl.append(gens[gi][0])
src=np.array(src); dst=np.array(dst); gl=np.array(gl)
taus=[1,-1,2,-2]; ti={t:i for i,t in enumerate(taus)}
def F(c):
    out=np.zeros_like(c)
    v=gl==0
    for k in range(4): np.add.at(out[:,k],src[v],c[dst[v],k])
    for l in taus:
        sel=gl==l
        # away steps: tau != l ; new tau = -l
        contrib=c[dst[sel],ti[-l]]/u
        for k in range(4):
            if taus[k]!=l: np.add.at(out[:,k],src[sel],contrib)
        # toward step: tau == l ; new tau any != -l
        mx=np.max(c[dst[sel]][:,[ti[t] for t in taus if t!=-l]],axis=1)
        np.add.at(out[:,ti[l]],src[sel],u*mx)
    return out
c=np.ones((N,4))
for it in range(iters):
    f=F(c); c=f/f.max()
f=F(c); r=f/c
print("ell",ell,"states",N,"u",u,"lam_cert",r.max(),"min",r.min(),"1/lam",1/r.max(),flush=True)
np.save('rho2_c_ell%d.npy'%ell,c)
