"""Z/2 dipole covers of square-tiled tori: explicit commuting approximations.

Base G = Z^2/Lambda, Lambda = <(N1,0),(C,N2)>; fiber Z/2; charges at 0 and g.
For each (lattice, g) we build the permutation pair (b,c) on 2N points, compute the
rectangle profile rho exactly (brute force), and build two commuting pairs:
  (P) path cut: cancel the dipole along a shortest lattice path (cost |g|_1);
  (T) thin cut: GL2(Z) change of basis (B,C)=(b^v1 c^v2, b^u1 c^u2) along the shortest
      primitive direction v of Lambda, band surgery on C, then back-substitution
      b''=B^alpha C''^beta, c''=B^gamma C''^delta.
We verify commutation and report rank distances rank(b''-b)+rank(c''-c).
usage: python3 surgery.py Nmin Nmax
"""
import sys, itertools
from math import gcd

def cycles(p):
    n=len(p); seen=[False]*n; k=0
    for i in range(n):
        if not seen[i]:
            k+=1; j=i
            while not seen[j]: seen[j]=True; j=p[j]
    return k
def comp(p,q): return [p[q[i]] for i in range(len(q))]   # p after q
def inv(p):
    r=[0]*len(p)
    for i,x in enumerate(p): r[x]=i
    return r
def pw(p,e):
    n=len(p); r=list(range(n)); q=p if e>=0 else inv(p)
    for _ in range(abs(e)): r=comp(q,r)
    return r
def rk(p,q): # rank(P-Q) = n - #cycles(P Q^-1)
    return len(p)-cycles(comp(p,inv(q)))

class Torus:
    def __init__(s,N1,N2,C):
        s.N1,s.N2,s.C=N1,N2,C; s.N=N1*N2
    def red(s,x,y):
        q=y//s.N2; y-=q*s.N2; x-=q*s.C; return (x%s.N1, y)
    def idx(s,x,y):
        x,y=s.red(x,y); return y*s.N1+x
    def coords(s,h): return (h%s.N1, h//s.N1)

def build(T,g):
    """beta,gamma: G->Z/2 with charge kappa = delta_0 + delta_g along an L-path."""
    N=T.N; beta=[0]*N; gamma=[0]*N
    gx,gy=T.coords(g)
    # choose shortest lift of g
    best=None
    for k in range(-N,N+1):
        for j in range(-2,3):
            a=gx-k*T.C+j*T.N1*1; b=gy+k*T.N2
            # (a,b) ~ g ?
            if T.idx(a,b)==g:
                if best is None or abs(a)+abs(b)<abs(best[0])+abs(best[1]): best=(a,b)
    # brute force over a window for the true L1-shortest lift
    for a in range(-N,N+1):
        for b in range(-N,N+1):
            if abs(a)+abs(b)<abs(best[0])+abs(best[1]) and T.idx(a,b)==g: best=(a,b)
    a,b=best
    # horizontal steps: flipping gamma at (i,0) moves charge between (i-1,0),(i,0)
    sx=1 if a>=0 else -1
    for i in range(0,a,sx):
        x0 = i+1 if sx>0 else i
        gamma[T.idx(x0,0)]^=1
    sy=1 if b>=0 else -1
    for j in range(0,b,sy):
        y0 = j+1 if sy>0 else j
        beta[T.idx(a,y0)]^=1
    return beta,gamma,abs(a)+abs(b)

def perms(T,beta,gamma):
    N=T.N; bp=[0]*(2*N); cp=[0]*(2*N)
    for h in range(N):
        x,y=T.coords(h)
        for e in (0,1):
            bp[2*h+e]=2*T.idx(x+1,y)+(e^beta[h])
            cp[2*h+e]=2*T.idx(x,y+1)+(e^gamma[h])
    return bp,cp

def kappa(T,beta,gamma):
    k=[0]*T.N
    for h in range(T.N):
        x,y=T.coords(h)
        k[h]=beta[h]^gamma[T.idx(x+1,y)]^gamma[h]^beta[T.idx(x,y+1)]
    return k

def order(p):
    n=len(p); o=1; seen=[False]*n
    for i in range(n):
        if not seen[i]:
            L=0;j=i
            while not seen[j]: seen[j]=True; j=p[j]; L+=1
            o=o*L//gcd(o,L)
    return o

def rho(bp,cp):
    ob,oc=order(bp),order(cp); best=0.0
    bs=[list(range(len(bp)))]
    for s in range(1,ob): bs.append(comp(bp,bs[-1]))
    cs=[list(range(len(cp)))]
    for t in range(1,oc): cs.append(comp(cp,cs[-1]))
    for s in range(1,ob):
        for t in range(1,oc):
            w=comp(comp(bs[s],cs[t]),inv(comp(cs[t],bs[s])))
            r=len(bp)-cycles(w)
            best=max(best,r/(s+t))
    return best

def thin(T,bp,cp):
    """GL2 change of basis along the shortest lattice direction + band surgery.
    Returns commuting (b2,c2) and the data used."""
    N=T.N
    best=None
    for a in range(-N,N+1):
        for b in range(-N,N+1):
            if (a,b)!=(0,0) and T.idx(a,b)==0 and (best is None or abs(a)+abs(b)<abs(best[0])+abs(best[1])):
                best=(a,b)
    k=gcd(abs(best[0]),abs(best[1])); v=(best[0]//k,best[1]//k)
    m=abs(v[0])+abs(v[1])+1; u=None
    for u1 in range(-m,m+1):
        for u2 in range(-m,m+1):
            if v[0]*u2-v[1]*u1==1 and (u is None or abs(u1)+abs(u2)<abs(u[0])+abs(u[1])): u=(u1,u2)
    B=comp(pw(bp,v[0]),pw(cp,v[1]))
    Cw=comp(pw(bp,u[0]),pw(cp,u[1]))
    base=lambda p,h: p[2*h]//2
    fib=lambda p,h: (p[2*h]%2)
    # the translation-cover structure: p(h,e)=(p(h),e+f(h))
    for p in (B,Cw):
        for h in range(N): assert p[2*h+1]==2*base(p,h)+(1^fib(p,h))
    Cinv=[0]*N
    for h in range(N): Cinv[base(Cw,h)]=h
    rowof=[-1]*N; rows=[]; h=0; j=0
    while rowof[h]<0:
        r=[]; x=h
        while rowof[x]<0: rowof[x]=j; r.append(x); x=base(B,x)
        rows.append(r); j+=1; h=base(Cw,h)
    H=len(rows); assert sum(len(r) for r in rows)==N
    eps=[sum(fib(B,x) for x in r)%2 for r in rows]
    cb=[base(Cw,h) for h in range(N)]; cf=[fib(Cw,h) for h in range(N)]
    seams=0
    if len(set(eps))>1:
        start=[j for j in range(H) if eps[j]!=eps[j-1]]
        for i,j0 in enumerate(start):
            j1=start[(i+1)%len(start)]; L=(j1-j0)%H
            if L==0: L=H
            for x in rows[(j1-1)%H]:
                y=cb[x]
                for _ in range(L): y=Cinv[y]
                cb[x]=y
            seams+=1
    # charges of (B, C'') and row-wise cancellation by changing C'' fibres
    def kap(x):  # fibre of B C'' vs C'' B at (x,0)
        return (cf[x]^fib(B,cb[x]))^(fib(B,x)^cf[base(B,x)])
    for x in range(N): assert cb[base(B,x)]==base(B,cb[x])
    for r in rows:
        for i in range(len(r)-1):
            if kap(r[i]): cf[r[i+1]]^=1
        assert kap(r[-1])==0 or len(r)==1 and kap(r[-1])==0, "row total nonzero"
    C2=[0]*(2*N)
    for h in range(N):
        for e in (0,1): C2[2*h+e]=2*cb[h]+(e^cf[h])
    assert comp(B,C2)==comp(C2,B)
    # back-substitute: e1 = u2*v - v2*u ; e2 = -u1*v + v1*u
    b2=comp(pw(B,u[1]),pw(C2,-v[1])); c2=comp(pw(B,-u[0]),pw(C2,v[0]))
    assert comp(b2,c2)==comp(c2,b2)
    return b2,c2,v,u,k,seams,rk(C2,Cw)

def pathcut(T,g):
    beta,gamma,L=build(T,g); return perms(T,[0]*T.N,[0]*T.N),L

if __name__=="__main__":
    a,b=int(sys.argv[1]),int(sys.argv[2]); worst=0
    for N in range(a,b+1):
        for N1 in range(1,N+1):
            if N%N1: continue
            for C in range(N1):
                T=Torus(N1,N//N1,C)
                for g in range(1,T.N):
                    beta,gamma,L=build(T,g)
                    k=kappa(T,beta,gamma); assert k[0]==1 and k[g]==1 and sum(k)==2
                    bp,cp=perms(T,beta,gamma)
                    r=rho(bp,cp)
                    b2,c2,v,u,kk,seams,rc=thin(T,bp,cp)
                    dth=rk(b2,bp)+rk(c2,cp)
                    b0,c0=perms(T,[0]*T.N,[0]*T.N); dpath=rk(b0,bp)+rk(c0,cp); assert dpath<=L
                    ub=min(dpath,dth)
                    worst=max(worst,ub/r)
                    print(N,N1,C,g,"rho=%.3f"%r,"path=%d"%dpath,"thin=%d"%dth,"v=",v,"k=",kk,"ub/rho=%.3f"%(ub/r))
    print("WORST ub/rho",worst)
