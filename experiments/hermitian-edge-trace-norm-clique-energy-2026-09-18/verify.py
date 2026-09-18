# Rigorous (interval) check that F(z) <= 1/|1-z| on the closed unit disc, z != 1,
# for F(z) = sum_{p<=q} c_pq w_pq Re(z^p zbar^q), w = 1 (p=q) or 2 (p<q), c_pq rational.
# Coefficients are rounded to multiples of 1e-7; all arithmetic is in floats with
# explicit outward padding (every bound is widened by 1e-12 relative + 1e-14 absolute).
import json, sys, math
from fractions import Fraction as Fr
PAD=1e-12
def up(x): return x+abs(x)*PAD+1e-14
def dn(x): return x-abs(x)*PAD-1e-14
def cos_range(a,b):
    # exact range of cos on [a,b], then padded
    lo=min(math.cos(a),math.cos(b)); hi=max(math.cos(a),math.cos(b))
    k=math.ceil(a/(2*math.pi))
    if 2*math.pi*k<=b: hi=1.0
    k=math.ceil((a-math.pi)/(2*math.pi))
    if math.pi+2*math.pi*k<=b: lo=-1.0
    return dn(lo),up(hi)
def load(fn,scale=1e7):
    J=json.load(open(fn)); C={}
    for k,v in J["coef"].items():
        p,q=map(int,k.split(",")); c=Fr(round(v*scale),int(scale))
        if (p,q)!=(0,0) and c<0: c=Fr(0)
        if c!=0: C[(p,q)]=c
    return J,C
def F_upper(C,r0,r1,t0,t1):
    s=0.0
    for (p,q),c in C.items():
        n=p+q; k=q-p; w=1 if p==q else 2
        cf=float(c)*w
        if n==0: s+=up(cf) if cf>0 else cf; continue
        R=(r0**n, r1**n)  # r in [0,1], monotone
        if k==0: cl,ch=1.0,1.0
        else: cl,ch=cos_range(k*t0,k*t1)
        # cf>=0 here; max of cf*R*cos over the box
        cands=[cf*R[0]*cl,cf*R[0]*ch,cf*R[1]*cl,cf*R[1]*ch]
        s+=up(max(cands))
    return up(s)
def h_lower(r0,r1,t0,t1):
    # |1-z|^2 = 1 + r^2 - 2 r cos t ; upper bound
    cl,ch=cos_range(t0,t1)
    m2=1+r1*r1-2*min(r0*cl,r1*cl,r0*ch,r1*ch)
    m2=up(max(m2,0.0))
    return dn(1/math.sqrt(m2)) if m2>0 else float('inf')
def verify(C,maxboxes=5_000_000):
    stack=[(0.0,1.0,0.0,math.pi,0)]; n=0; worst=float('inf')
    while stack:
        r0,r1,t0,t1,d=stack.pop(); n+=1
        if n>maxboxes: return False,n,worst
        g=h_lower(r0,r1,t0,t1)-F_upper(C,r0,r1,t0,t1)
        if g>0: worst=min(worst,g); continue
        if d>60: return False,n,(r0,r1,t0,t1)
        if (r1-r0)>(t1-t0)/math.pi*1.0:
            rm=(r0+r1)/2; stack+= [(r0,rm,t0,t1,d+1),(rm,r1,t0,t1,d+1)]
        else:
            tm=(t0+t1)/2; stack+= [(r0,r1,t0,tm,d+1),(r0,r1,tm,t1,d+1)]
    return True,n,worst
if __name__=="__main__":
    J,C=load(sys.argv[1])
    ok,n,w=verify(C)
    F1=sum(c*(1 if p==q else 2) for (p,q),c in C.items()); c00=C.get((0,0),Fr(0))
    print(sys.argv[1],"verified" if ok else "FAILED",n,"boxes; min gap",w)
    print(" coefficients:",{f"{p},{q}":str(c) for (p,q),c in sorted(C.items())})
    print(" c00 =",c00,"F(1) =",F1)
    for m in range(4,41):
        L=c00*m*m-m*F1; T2=Fr(3,4)*(m-1)**4  # need L >= (sqrt3/2)(m-1)^2 <=> L>0 and L^2 >= 3/4 (m-1)^4
        good = L>0 and L*L>=T2
        if m<=12 or m%10==0: print("  m=%d  c00 m^2 - m F(1) = %.5f  target %.5f  %s"%(m,float(L),math.sqrt(3)/2*(m-1)**2,"OK" if good else "no"))
    # tail: Q(m) = (c00 - s/2) m^2 + (s - F(1)) m - s/2 >= 0 for all m >= 6, s = sqrt3,
    # using rational bounds sL < sqrt3 < sU (checked by squaring).
    sL,sU=Fr(17320508,10**7),Fr(17320509,10**7); assert sL*sL<3<sU*sU
    a=c00-sU/2; b=sL-F1; c=-sU/2      # Q(m) >= a m^2 + b m + c for m >= 0
    Q6=a*36+b*6+c; dQ6=2*a*6+b
    print(" tail: a=%.6f (>0: %s), Q(6)>=%.6f, Q'(6)>=%.6f  => Q(m)>=0 for all m>=6: %s"%(float(a),a>0,float(Q6),float(dQ6),a>0 and Q6>=0 and dQ6>=0))
