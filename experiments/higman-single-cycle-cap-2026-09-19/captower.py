# Explicit b-trivial single-cycle models of H(n1, 3^mb, 3^mc, 3^md) at level cap(m) = g(mb)+v2(mc)+v2(md)+4,
# g(mb) = v2(3^mb - 1).  Function composition, relations  a b a^-1 = b^n1, b c b^-1 = c^n2, c d c^-1 = d^n3,
# d a d^-1 = a^n4  (= the right-action relations b^a = b^n1 etc. of H(n1,n2,n3,n4)).
# a = x+1, b = 1, d = x*3^md, and on the layer 2^v*U of valuation v, in log coordinates y = s*3^i (s = +-1),
# c(2^v s 3^i) = 2^v s 3^lam(i), lam(r + md*q) = r + n3*md*q  (0 <= r < md).   Usage: captower.py mb mc md [n1]
import sys
def v2(x):
    x=abs(x); r=0
    while x%2==0: x//=2; r+=1
    return r
def build(k,mb,mc,md):
    N=1<<k; n3=pow(3,mc); n4=pow(3,md)
    a=[(x+1)%N for x in range(N)]; b=list(range(N)); d=[(x*n4)%N for x in range(N)]
    c=list(range(N))
    for v in range(k):
        n=k-v                          # units mod 2^n
        if n<3: continue               # c = id on layers with |U| <= 2
        M=1<<n; L=1<<(n-2)             # |<3>| = L
        if md>=L: continue             # d trivial on this layer: c = id
        pw=[1]*L
        for i in range(1,L): pw[i]=pw[i-1]*3%M
        for s in (1,M-1):
            for i in range(L):
                r,q=i%md,i//md
                lam=(r+n3*md*q)%L
                x=(s*pw[i]%M)<<v; y=(s*pw[lam]%M)<<v
                c[x%N]=y%N
    return a,b,c,d
def comp(f,g): return [f[g[x]] for x in range(len(f))]
def inv(f):
    r=[0]*len(f)
    for x,y in enumerate(f): r[y]=x
    return r
def pw(f,e):
    N=len(f); o=1; g=f
    while True:
        h=g
        if h==list(range(N)): break
        g=comp(f,g); o+=1
    e%=o; r=list(range(N))
    for _ in range(e): r=comp(f,r)
    return r
def isW(f,k):
    for r in range(1,k+1):
        m=1<<r
        img={}
        for x in range(len(f)):
            if img.setdefault(x%m,f[x]%m)!=f[x]%m: return False
    return True
def check(k,mb,mc,md,n1=3):
    a,b,c,d=build(k,mb,mc,md)
    n2,n3,n4=pow(3,mb),pow(3,mc),pow(3,md)
    ok=all(len(set(g))==len(g) and isW(g,k) for g in (a,b,c,d))
    rel=[comp(comp(x,y),inv(x))==pw(y,n) for x,y,n in ((a,b,n1),(b,c,n2),(c,d,n3),(d,a,n4))]
    return ok and all(rel), rel
if __name__=="__main__":
    mb,mc,md=map(int,sys.argv[1:4]); n1=int(sys.argv[4]) if len(sys.argv)>4 else 3
    cap=v2(pow(3,mb)-1)+v2(mc)+v2(md)+4
    for k in range(1,cap+1):
        good,rel=check(k,mb,mc,md,n1)
        if not good: print("FAIL at",k,rel); break
    else: print("m=(%d,%d,%d) n1=%d: b-trivial single-cycle model verified at every level 1..%d = cap"%(mb,mc,md,n1,cap))
