# Exact integer verification of the Busemann-weighted Schur certificate:
# F(c) <= lam * c componentwise on (states x tau) with u = UN/UD rational.
import sys, numpy as np
from fractions import Fraction
exec(open('rho2v.py').read().split("c=np.ones((N,4))")[0])   # builds states, src, dst, gl, taus, ti, F (float), with ell,u from argv
UN,UD=map(int,sys.argv[4].split('/')); lamF=Fraction(sys.argv[5])
c=np.ones((N,4))
for it in range(iters):
    f=F(c); c=f/f.max()
print("float lam",(F(c)/c).max())
S=10**9
ci=np.ceil(c*S).astype(np.int64)+1     # integer weights
assert ci.max()<=S+1
# integer F scaled by UN*UD:  vertical: UN*UD*c ; toward: UN*UN*c ; away: UD*UD*c
out=np.zeros_like(ci)
v=gl==0
for k in range(4): np.add.at(out[:,k],src[v],UN*UD*ci[dst[v],k])
for l in taus:
    sel=gl==l
    contrib=UD*UD*ci[dst[sel],ti[-l]]
    for k in range(4):
        if taus[k]!=l: np.add.at(out[:,k],src[sel],contrib)
    mx=np.max(ci[dst[sel]][:,[ti[t] for t in taus if t!=-l]],axis=1)
    np.add.at(out[:,ti[l]],src[sel],UN*UN*mx)
assert out.max() < 2**62
# check out <= lam*UN*UD*ci  with lam = a/b  <=>  b*out <= a*UN*UD*ci  (python ints to avoid overflow)
a,b=lamF.numerator,lamF.denominator
ok=all(b*int(o) <= a*UN*UD*int(x) for o,x in zip(out.ravel(),ci.ravel()))
worst=max(Fraction(int(o),UN*UD*int(x)) for o,x in zip(out.ravel(),ci.ravel()))
print("ell",ell,"u",UN,"/",UD,"states",N,"exact max ratio",float(worst),"<= lam",lamF,":",ok)
