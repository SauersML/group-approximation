# Floating-point LP that FINDS a kernel certificate for the odd antihole C_n-bar (n = 2k+1).
# Not part of the proof: verify_ah.py checks the output rigorously.
#
# Unknowns: a matching y_delta >= 0 (delta = 2..k, cyclic distance), 2 sum_delta y_delta = 1, and real
# coefficients f_pq(s), s = 0..k, 0 <= p <= q <= D, defining K(s,z) = sum_{p<=q} w_pq f_pq(s) Re(z^p zbar^q),
# w = 1 (p = q) or 2 (p < q).  Constraints (on a polar grid of the unit disc):
#   non-edges  s = 1:        K(1,z) <= -eps
#   edges      s = 2..k:     K(s,z) <= (1-eta) 2 y_s / |1-z|
#   (p,q) != (0,0), t=0..k:  fhat_pq(t) = f_pq(0) + 2 sum_{s>=1} f_pq(s) cos(2 pi s t/n) >= 0
# Objective (the bound on ||C||_1):  n ( 2 sum_{s>=1} f_00(s) - sum_{(p,q)!=(0,0)} w_pq f_pq(0) ).
# Usage: python3 cert_ah.py n D eta eps out.json
import numpy as np, sys, json
from scipy.optimize import linprog
n=int(sys.argv[1]); D=int(sys.argv[2]); eta=float(sys.argv[3]); eps=float(sys.argv[4]); out=sys.argv[5]
k=(n-1)//2
pairs=[(p,q) for p in range(D+1) for q in range(p,D+1)]
NP=len(pairs); S=k+1
nv=(k-1)+NP*S
def fi(pi,s): return (k-1)+pi*S+s
rs=np.linspace(0,1,61); ts=np.linspace(0,np.pi,481)
A=[];b=[]
for s in range(1,k+1):
    for r in rs:
        for t in ts:
            z=r*np.exp(1j*t); row=np.zeros(nv)
            for pi,(p,q) in enumerate(pairs):
                row[fi(pi,s)]=(1.0 if p==q else 2.0)*r**(p+q)*np.cos((q-p)*t)
            if s==1: A.append(row); b.append(-eps)
            else:
                if abs(1-z)<1e-4: continue
                row[s-2]-=2*(1-eta)/abs(1-z); A.append(row); b.append(0.0)
for pi,(p,q) in enumerate(pairs):
    if (p,q)==(0,0): continue
    for t in range(k+1):
        row=np.zeros(nv)
        for s in range(S): row[fi(pi,s)]=-(1 if s==0 else 2)*np.cos(2*np.pi*s*t/n)
        A.append(row); b.append(0.0)
Aeq=np.zeros((1,nv)); Aeq[0,:k-1]=2
c=np.zeros(nv)
for s in range(1,k+1): c[fi(0,s)]-=2*n
for pi,(p,q) in enumerate(pairs):
    if (p,q)!=(0,0): c[fi(pi,0)]+=n*(1.0 if p==q else 2.0)
bnds=[(0,None)]*(k-1)+[(-50,50)]*(NP*S)
res=linprog(c,A_ub=np.array(A),b_ub=np.array(b),A_eq=Aeq,b_eq=[1.0],bounds=bnds,method='highs')
val=-res.fun
print(res.message)
print("n=%d D=%d eta=%g eps=%g  LP value %.5f  need sqrt3(n-2) = %.5f"%(n,D,eta,eps,val,np.sqrt(3)*(n-2)))
x=res.x
J={"n":n,"D":D,"eta":eta,"eps":eps,"lp_value":val,"y":{str(d):x[d-2] for d in range(2,k+1)},
   "f":{"%d,%d,%d"%(p,q,s):x[fi(pi,s)] for pi,(p,q) in enumerate(pairs) for s in range(S)}}
json.dump(J,open(out,"w"),indent=1)
