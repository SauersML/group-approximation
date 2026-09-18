# Exact Collatz-Wielandt certificate for the star-stage GW mean matrix.
import sys, numpy as np
from fractions import Fraction
fn=sys.argv[1]; p=Fraction(sys.argv[2]); lam0=Fraction(sys.argv[3]); q=1-p
rows={}; ent={}
with open(fn) as f:
    hdr=f.readline().strip()
    for line in f:
        _,s,g,_,t,cb,i,j,c=line.split()
        r=(int(s),int(g)); col=(int(t),int(cb))
        e=ent.setdefault(r,{}).setdefault(col,{})
        e[(int(i),int(j))]=e.get((int(i),int(j)),0)+int(c)
types=sorted(set(ent)|{c for d in ent.values() for c in d}); idx={x:k for k,x in enumerate(types)}; n=len(types)
pw={}
def w(i,j):
    if (i,j) not in pw: pw[(i,j)]=p**i*q**j
    return pw[(i,j)]
Mx={}
for r,d in ent.items():
    for col,dd in d.items():
        Mx[(idx[r],idx[col])]=sum(c*w(i,j) for (i,j),c in dd.items())
# communicating class of the singleton type (a,{0})
adj={k:set() for k in range(n)}
for (a,b) in Mx: adj[a].add(b)
def reach(src,adj):
    seen={src}; st=[src]
    while st:
        x=st.pop()
        for y in adj[x]:
            if y not in seen: seen.add(y); st.append(y)
    return seen
s0=idx[(0,1)]
fwd=reach(s0,adj)
radj={k:set() for k in range(n)}
for (a,b) in Mx: radj[b].add(a)
bwd=reach(s0,radj)
cls=sorted(fwd&bwd); ci={k:m for m,k in enumerate(cls)}; m=len(cls)
Mf=np.zeros((m,m))
for (a,b),v in Mx.items():
    if a in ci and b in ci: Mf[ci[a],ci[b]]=float(v)
v=np.ones(m)
for _ in range(5000): v=Mf@v; v/=v.max()
print(hdr,"| types",n,"class size",m,"float perron",max(abs(np.linalg.eigvals(Mf))))
vq=[Fraction(int(x*10**12)+1,10**12) for x in v]
ratios=[]
for a in cls:
    tot=sum(val*vq[ci[b]] for (aa,b),val in Mx.items() if aa==a and b in ci)
    ratios.append(tot/vq[ci[a]])
mr=min(ratios)
print("exact min (Mv)_k/v_k over class =",float(mr),"certifies rho(M) >=",lam0,":",mr>=lam0)
