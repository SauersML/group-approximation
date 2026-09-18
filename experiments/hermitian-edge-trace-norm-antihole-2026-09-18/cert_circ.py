# generalisation of cert_ah.py to any circulant graph on Z_n: edges at distances in EDGES
# usage: python3 cert_circ.py n D eta eps EDGES(comma) alpha out.json
import numpy as np, sys, json
from scipy.optimize import linprog
n=int(sys.argv[1]); D=int(sys.argv[2]); eta=float(sys.argv[3]); eps=float(sys.argv[4])
EDG=[int(v) for v in sys.argv[5].split(',')]; alpha=int(sys.argv[6]); out=sys.argv[7]
h=n//2; mult=lambda s: 1 if 2*s==n else 2
NON=[s for s in range(1,h+1) if s not in EDG]
pairs=[(p,q) for p in range(D+1) for q in range(p,D+1)]
NP=len(pairs); S=h+1; NY=len(EDG)
nv=NY+NP*S
def fi(pi,s): return NY+pi*S+s
rs=np.linspace(0,1,41); ts=np.linspace(0,np.pi,321)
A=[];b=[]
Rg,Tg=np.meshgrid(rs,ts,indexing='ij'); Rg=Rg.ravel(); Tg=Tg.ravel(); Z=Rg*np.exp(1j*Tg)
basis=np.array([(1.0 if p==q else 2.0)*Rg**(p+q)*np.cos((q-p)*Tg) for (p,q) in pairs]).T
for s in range(1,h+1):
    blk=np.zeros((len(Rg),nv)); blk[:,[fi(pi,s) for pi in range(NP)]]=basis
    if s in NON:
        A.append(blk); b.append(-eps*np.ones(len(Rg)))
    else:
        ok=np.abs(1-Z)>1e-4; blk=blk[ok]; blk[:,EDG.index(s)]-=2*(1-eta)/np.abs(1-Z[ok])
        A.append(blk); b.append(np.zeros(len(blk)))
for pi,(p,q) in enumerate(pairs):
    if (p,q)==(0,0): continue
    row=np.zeros((h+1,nv))
    for t in range(h+1):
        for s in range(S): row[t,fi(pi,s)]=-(1 if s==0 else mult(s))*np.cos(2*np.pi*s*t/n)
    A.append(row); b.append(np.zeros(h+1))
A=np.vstack(A); b=np.concatenate(b)
Aeq=np.zeros((1,nv)); Aeq[0,:NY]=[mult(s) for s in EDG]
c=np.zeros(nv)
for s in range(1,h+1): c[fi(0,s)]-=n*mult(s)
for pi,(p,q) in enumerate(pairs):
    if (p,q)!=(0,0): c[fi(pi,0)]+=n*(1.0 if p==q else 2.0)
bnds=[(0,None)]*NY+[(-50,50)]*(NP*S)
res=linprog(c,A_ub=A,b_ub=b,A_eq=Aeq,b_eq=[1.0],bounds=bnds,method='highs')
val=-res.fun
print("n=%d EDG=%s D=%d LP %.4f need sqrt3(n-alpha)=%.4f ratio %.4f"%(n,EDG,D,val,np.sqrt(3)*(n-alpha),val/(np.sqrt(3)*(n-alpha))),flush=True)
x=res.x
json.dump({"n":n,"D":D,"edges":EDG,"alpha":alpha,"lp_value":val,"y":{str(s):x[i] for i,s in enumerate(EDG)},
  "f":{"%d,%d,%d"%(p,q,s):x[fi(pi,s)] for pi,(p,q) in enumerate(pairs) for s in range(S)}},open(out,"w"))
