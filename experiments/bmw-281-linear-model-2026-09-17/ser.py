# power series mod s^m over F3, as tuples; helpers
def mul(a,b,m):
    r=[0]*m
    for i in range(m):
        if a[i]:
            for j in range(m-i): r[i+j]=(r[i+j]+a[i]*b[j])%3
    return r
def inv(a,m):
    r=[0]*m; r[0]=a[0]
    for k in range(1,m):
        s=sum(a[i]*r[k-i] for i in range(1,k+1))%3
        r[k]=(-s*r[0])%3
    return r
def add(a,b): return [(x+y)%3 for x,y in zip(a,b)]
def sub(a,b): return [(x-y)%3 for x,y in zip(a,b)]
def sig(a): return [(a[i]*(-1)**i)%3 for i in range(len(a))]
def is_mob(p, m, pts, idx):
    """p: list mapping point index -> point index on O/s^m. Return (tw,al,be,ga) or None, with delta=1."""
    for tw in (0,1):
        q = (lambda x: sig(x)) if tw else (lambda x: x)
        # p(x) = (al*q(x)+be)/(ga*q(x)+1); points x with q(x)=0,1,-1
        z=[0]*m; one=[1]+[0]*(m-1); mone=[2]+[0]*(m-1)
        P0 = pts[p[idx(z)]]; P1 = pts[p[idx(q(one))]]; Pm = pts[p[idx(q(mone))]]
        be = list(P0)
        d = sub(P1,Pm)
        if d[0]==0: return None
        ga = mul(sub(sub(add(be,be),P1),Pm), inv(d,m), m)
        al = sub(mul(P1, add(ga,one), m), be)
        if ga[0]!=0: continue
        ok=True
        for i,x in enumerate(pts):
            y = q(list(x))
            v = mul(add(mul(al,y,m),be), inv(add(mul(ga,y,m),one),m), m)
            if idx(v)!=p[i]: ok=False; break
        if ok: return (tw,al,be,ga)
    return None
