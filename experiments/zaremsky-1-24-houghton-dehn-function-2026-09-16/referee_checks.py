"""Referee checks (2026-09-16) for notes/zaremsky-1-24-houghton-dehn-function-swarm-2026-09-16.md.
Part 1: free-group bookkeeping in the proofs of Lemma (a)-(e) (exact free reduction / cyclic conjugacy).
Part 2: independent permutation checks of the group identities used (right actions, truncated rays).
Letters: x = g_1, y = g_2, a = alpha; capitals are inverses."""
def red(w):
    s=[]
    for c in w:
        if s and s[-1]==c.swapcase(): s.pop()
        else: s.append(c)
    return ''.join(s)
def inv(w): return ''.join(c.swapcase() for c in reversed(w))
def pw(c,k): return c*k if k>=0 else c.swapcase()*(-k)
def a(j): return pw('x',j)+'a'+pw('x',-j)
def rho(j): return pw('x',j)+'y'+pw('x',-j)
def conj(w,h): return inv(h)+w+h   # w^h
def cycl_conj(u,v):  # is u a free conjugate of v (cyclic reductions equal up to rotation)?
    def cr(w):
        w=red(w)
        while len(w)>1 and w[0]==w[-1].swapcase(): w=w[1:-1]
        return w
    u,v=cr(u),cr(v)
    return len(u)==len(v) and (u in v+v)
ok=True
for d in range(3,20):
    # (a) rho_2^-1 a_d rho_2 freely = x^2 (Y a_{d-2} y) x^-2
    ok&= red(conj(a(d),rho(2)))==red(pw('x',2)+'Y'+a(d-2)+'y'+pw('x',-2))
    ok&= red(pw('x',2)+a(d-3)+pw('x',-2))==red(a(d-1))
for d in range(1,20):
    Qrel='Y'+a(d)+'y'+inv(a(d-1))
    tgt=conj('a',rho(-d))+inv(a(-1))
    ok&= red(conj(Qrel,pw('x',d)))==red(tgt)
for i in range(2,20):
    ok&= cycl_conj('A'+inv(a(-i))+'a'+a(-i), inv('A'+inv(a(i))+'a'+a(i))) or cycl_conj('A'+inv(a(-i))+'a'+a(-i), 'A'+inv(a(i))+'a'+a(i))
for k in range(1,20):
    ok&= red(pw('y',k)+'a'+pw('y',-k))==red('y'+pw('y',k-1)+'a'+pw('y',-(k-1))+'Y')
    # Q(k) conj by g2: y (Y a_k y a_{k-1}^-1) Y = a_k y a_{k-1}^-1 Y
    ok&= cycl_conj('Y'+a(k)+'y'+inv(a(k-1)), a(k)+inv('y'+a(k-1)+'Y'))
# Lemma (e): a_d rho_{d+1} rho_d^{-1} is freely conjugate to the bounded word alpha g1 g2 g1^-1 g2^-1
for d in range(-10,10):
    w=a(d)+rho(d+1)+inv(rho(d))
    ok&= red(conj(w,pw('x',d)))==red('a'+'x'+'y'+'X'+'Y')
print('FREE OK' if ok else 'FREE FAIL')
free_ok=ok

# ---- Part 2 ----
N=80
pts=[(r,p) for r in (1,2,3) for p in range(1,N+1)]
def lam(a,b):
    def f(x):
        r,p=x
        if r==a: return (a,p-1) if p>=2 else (b,1)
        if r==b: return (b,p+1)
        return x
    return f
def invf(f):
    # valid on points far from truncation boundary
    t={}
    for r in (1,2,3):
        for p in range(1,N+5): t[f((r,p))]=(r,p)
    return lambda x:t[x]
G={'x':lam(1,2),'y':lam(1,3),'a':lambda z:(1,2) if z==(1,1) else ((1,1) if z==(1,2) else z)}
G['X']=invf(G['x']); G['Y']=invf(G['y']); G['A']=G['a']
def ev(w,x):
    for c in w: x=G[c](x)
    return x
def pw(c,k): return c*k if k>=0 else c.swapcase()*(-k)
def a(j): return pw('x',j)+'a'+pw('x',-j)
def rho(j): return pw('x',j)+'y'+pw('x',-j)
def inv(w): return ''.join(c.swapcase() for c in reversed(w))
def same(u,v,dep=35): return all(ev(u,x)==ev(v,x) for x in pts if x[1]<=dep)
ok=True
for d in range(1,12):
    ok&=same(rho(-d), ''.join(a(-i) for i in range(d,0,-1))+rho(0))
    ok&=same(inv(rho(-d))+'a'+rho(-d), a(-1))
    ok&=same('Y'+a(d)+'y', a(d-1))
for d in range(2,12):
    ok&=same(inv(rho(d))+'a'+rho(d),'a')
    ok&=same(rho(d), ''.join(a(i) for i in range(d-1,1,-1))+rho(2))
for d in range(-8,9): ok&=same(a(d), rho(d)+inv(rho(d+1)))
ok&=same(inv(a(-1)+rho(0))+'a'+a(-1)+rho(0), a(-1))
for k in range(0,12): ok&=same(pw('y',k)+'a'+pw('y',-k), a(k))
ok&=same('axyXY','')
print('PERM OK' if ok else 'PERM FAIL')
print('ALL OK' if (ok and free_ok) else 'SOME FAILURE')
