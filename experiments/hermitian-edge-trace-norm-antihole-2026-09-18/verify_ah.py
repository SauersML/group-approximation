# Rigorous check of a kernel certificate for the odd antihole C_n-bar (the only computer step of the
# n = 13 case in research/hermitian-edge-trace-norm-odd-antihole-facets-proof.md).
# Input: JSON from cert_ah.py.  Steps:
#  1. Round y and f to multiples of 1e-7 (exact Fractions); rescale nothing, but fix y_k so that
#     2 sum_delta y_delta = 1 exactly; check y >= 0.
#  2. Circulant PSD: for (p,q) != (0,0) and t = 0..k, a rigorous (mpmath interval) lower bound of
#     fhat_pq(t) = f_pq(0) + 2 sum_{s>=1} f_pq(s) cos(2 pi s t / n).  If some lower bound is < 0, raise
#     f_pq(0) by a rational amount so that every fhat_pq(t) >= 0 (this only changes K(0, .)).
#  3. Interval branch-and-bound over (r, theta) in [0,1] x [0,pi] (K(s, zbar) = K(s, z)):
#       s = 1:      K(1,z) < 0                    on the closed disc,
#       s = 2..k:   K(s,z) < 2 y_s / |1 - z|      on the closed disc minus {1}.
#     Float arithmetic with every bound widened outward by 1e-12 relative + 1e-14 absolute.
#  4. The exact bound  beta n,  beta = 2 sum_{s>=1} f_00(s) - sum_{(p,q)!=(0,0)} w_pq f_pq(0),
#     compared with sqrt3 (n-2) by squaring.
import json, sys, math
from fractions import Fraction as Fr
import mpmath
from mpmath import iv
iv.dps=40
PAD=1e-12
def up(x): return x+abs(x)*PAD+1e-14
def dn(x): return x-abs(x)*PAD-1e-14
def cos_range(a,b):
    lo=min(math.cos(a),math.cos(b)); hi=max(math.cos(a),math.cos(b))
    kk=math.ceil(a/(2*math.pi))
    if 2*math.pi*kk<=b: hi=1.0
    kk=math.ceil((a-math.pi)/(2*math.pi))
    if math.pi+2*math.pi*kk<=b: lo=-1.0
    return dn(lo),up(hi)
J=json.load(open(sys.argv[1])); n=J["n"]; D=J["D"]; k=(n-1)//2
SC=10**7
def rnd(v): return Fr(round(v*SC),SC)
y={int(d):rnd(v) for d,v in J["y"].items()}
for d in y:
    if y[d]<0: y[d]=Fr(0)
y[k]=Fr(1,2)-sum(y[d] for d in y if d!=k)
assert all(v>=0 for v in y.values()) and 2*sum(y.values())==1
f={}
for key,v in J["f"].items():
    p,q,s=map(int,key.split(",")); f[(p,q,s)]=rnd(v)
pairs=sorted({(p,q) for (p,q,s) in f})
w=lambda p,q: 1 if p==q else 2
# ---- step 2: circulant PSD
bumped={}
for (p,q) in pairs:
    if (p,q)==(0,0): continue
    worst=None
    for t in range(k+1):
        val=iv.mpf(f[(p,q,0)].numerator)/f[(p,q,0)].denominator
        for s in range(1,k+1):
            c=f[(p,q,s)]
            val+=2*(iv.mpf(c.numerator)/c.denominator)*iv.cos(2*iv.pi*s*t/n)
        lo=float(mpmath.mpf(val.a))
        worst=lo if worst is None else min(worst,lo)
    if worst<0:
        bump=Fr(math.ceil(-worst*1e9)+1,10**9); f[(p,q,0)]+=bump; bumped[(p,q)]=bump
# ---- step 3: disc inequalities
def K_upper(s,r0,r1,t0,t1):
    tot=0.0
    for (p,q) in pairs:
        cf=float(f[(p,q,s)])*w(p,q)
        if cf==0: continue
        N=p+q; kk=q-p
        if N==0: tot=up(tot+up(cf)); continue
        R=(r0**N, r1**N)
        cl,ch=(1.0,1.0) if kk==0 else cos_range(kk*t0,kk*t1)
        tot=up(tot+up(max(cf*R[0]*cl,cf*R[0]*ch,cf*R[1]*cl,cf*R[1]*ch)))
    return tot
def h_lower(r0,r1,t0,t1):
    cl,ch=cos_range(t0,t1)
    m2=up(1+r1*r1-2*dn(min(r0*cl,r1*cl,r0*ch,r1*ch)))
    return dn(1/math.sqrt(m2)) if m2>0 else float('inf')
def verify_s(s,maxboxes=20_000_000):
    stack=[(0.0,1.0,0.0,math.pi,0)]; nb=0; gap=float('inf')
    ys=float(y[s]) if s>=2 else 0.0
    while stack:
        r0,r1,t0,t1,d=stack.pop(); nb+=1
        if nb>maxboxes: return False,nb,gap
        rhs=dn(2*dn(ys)*h_lower(r0,r1,t0,t1)) if s>=2 else 0.0
        g=rhs-K_upper(s,r0,r1,t0,t1)
        if g>0: gap=min(gap,g); continue
        if d>60: return False,nb,(r0,r1,t0,t1)
        if (r1-r0)>(t1-t0)/math.pi:
            rm=(r0+r1)/2; stack+=[(r0,rm,t0,t1,d+1),(rm,r1,t0,t1,d+1)]
        else:
            tm=(t0+t1)/2; stack+=[(r0,r1,t0,tm,d+1),(r0,r1,tm,t1,d+1)]
    return True,nb,gap
allok=True
for s in range(1,k+1):
    ok,nb,gap=verify_s(s); allok&=ok
    print(" s=%d (%s): %s, %d boxes, min gap %s"%(s,"non-edge K<0" if s==1 else "edge K<2y/|1-z|","verified" if ok else "FAILED",nb,gap),flush=True)
beta=2*sum(f[(0,0,s)] for s in range(1,k+1))-sum(w(p,q)*f[(p,q,0)] for (p,q) in pairs if (p,q)!=(0,0))
B=n*beta
ok_bound = B>0 and B*B>=3*(n-2)**2
print(sys.argv[1],"n=%d D=%d"%(n,D))
print(" y =",{d:str(v) for d,v in sorted(y.items())})
print(" f_pq(0) bumped for circulant PSD:",{f"{p},{q}":str(v) for (p,q),v in bumped.items()} or "none")
print(" bound n*beta = %s = %.6f ; need sqrt3(n-2) = %.6f ; n*beta >= sqrt3(n-2): %s"%(B,float(B),math.sqrt(3)*(n-2),ok_bound))
print("RESULT:", "CERTIFIED ||C||_1 >= %.6f >= sqrt3(n-2) on C_%d-bar"%(float(B),n) if (allok and ok_bound) else "NOT CERTIFIED")
json.dump({"n":n,"D":D,"y":{str(d):str(v) for d,v in y.items()},"f":{"%d,%d,%d"%kk:str(v) for kk,v in f.items()}},open(sys.argv[1].replace(".json","_exact.json"),"w"),indent=1)
