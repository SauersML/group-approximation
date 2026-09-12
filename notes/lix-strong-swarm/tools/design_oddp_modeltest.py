# lx-design model tests (odd primes): constants, the twisted resolution map A_r, slot permutation
# conjugation, and the surviving index pairs of the even Cartan sum under the vanishing lemma V.
import itertools, sys
def primes(n): return [q for q in range(3,n) if all(q%d for d in range(2,int(q**.5)+1))]
fails=0; checks=0
def ok(c,msg):
    global fails,checks; checks+=1
    if not c: fails+=1; print("FAIL",msg)
# T1: c_q = (-1)^{m q(q-1)/2} (m!)^q ; c_1 = m!, c_2 = -1, c_{2k} = (-1)^k ; kappa(1,1)=(-1)^m ; c_2 = kappa(1,1) c_1^2
from math import factorial
for p in primes(102):
    m=(p-1)//2
    c=lambda q: (pow(-1,(m*q*(q-1))//2)*pow(factorial(m),q,p))%p
    ok(c(1)==factorial(m)%p,f"c1 p={p}")
    ok(c(2)==(p-1),f"c2=-1 p={p}")
    for k in range(1,8): ok(c(2*k)==pow(-1,k,p)%p if k%2==0 else c(2*k)==p-1,f"c2k p={p} k={k}")
    ok((pow(-1,m)*factorial(m)**2)%p==p-1,f"wilson kappa c1^2 p={p}")
    # riffle sign for 2p slots of degree 1: inversions p(p-1)/2
    ok(pow(-1,p*(p-1)//2)==pow(-1,m),f"riffle sign p={p}")
# group ring F_p[C_p] as length-p coefficient lists; T^i = e_i
def mul(a,b,p):
    c=[0]*p
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                if y: c[(i+j)%p]=(c[(i+j)%p]+x*y)%p
    return c
def T(i,p): v=[0]*p; v[i%p]=1; return v
def theta(a,r,p):  # T -> T^r
    c=[0]*p
    for i,x in enumerate(a): c[(i*r)%p]=(c[(i*r)%p]+x)%p
    return c
def add(a,b,p): return [(x+y)%p for x,y in zip(a,b)]
def scal(s,a,p): return [(s*x)%p for x in a]
def aug(a,p): return sum(a)%p
for p in [3,5,7,11,13]:
    one=T(0,p); gS=add(T(1,p),scal(p-1,one,p),p); gN=[1]*p
    altCoeff=lambda i: gS if i%2==0 else gN   # d : W_{i+1} -> W_i is left mult by altCoeff i
    for r in range(1,p):
        rho=[0]*p
        for i in range(r): rho=add(rho,T(i,p),p)
        def A(i):  # coefficient of A_r(e_i) = A(i) e_i
            k=i//2
            return scal(pow(r,k,p),one,p) if i%2==0 else scal(pow(r,k,p),rho,p)
        for i in range(0,12):
            # chain map, theta-semilinear:  d(A(e_{i+1})) = theta(altCoeff i) * A(e_i)
            lhs=mul(A(i+1),altCoeff(i),p)      # d(A e_{i+1}) = A(i+1)*altCoeff(i) e_i  (commutative ring)
            rhs=mul(theta(altCoeff(i),r,p),A(i),p)
            ok(lhs==rhs,f"A_r chain p={p} r={r} i={i}")
            k=i//2; ok(aug(A(i),p)==(pow(r,k,p) if i%2==0 else pow(r,k+1,p)),f"aug p={p} r={r} i={i}")
        ok(A(0)==one,f"A0 id p={p} r={r}")
# T3: slot permutation sigma_r t = t o pi^{-1}, pi(i)=r i ; rotation R t = t o (i -> i-1)  (or +1)
for p in [3,5,7,11]:
    for r in range(1,p):
        rinv=pow(r,-1,p)
        for sgn in (+1,-1):
            rot=lambda t,s=1: tuple(t[(i-sgn*s)%p] for i in range(p))
            sig=lambda t: tuple(t[(i*rinv)%p] for i in range(p))
            for t in itertools.islice(itertools.product(range(3),repeat=p),200):
                ok(sig(rot(t))==rot(sig(t),r),f"sigma T = T^r sigma p={p} r={r} conv={sgn}")
# T4: even classes, degrees 2k,2k'; index j=2(k+k'-i)(p-1).  V: D_a nonzero only if a = 0 or -1 mod 2(p-1).
# surviving pairs (a,b), a+b=j, a<=2k(p-1), b<=2k'(p-1): must be exactly a=2s'(p-1), b=2s''(p-1)
for p in [3,5,7,11]:
    L=2*(p-1)
    for k in range(0,5):
        for kk in range(0,5):
            for i in range(0,k+kk+1):
                j=2*(k+kk-i)*(p-1)
                surv=[(a,j-a) for a in range(0,j+1) if a<=2*k*(p-1) and j-a<=2*kk*(p-1)
                      and a%L in (0,L-1) and (j-a)%L in (0,L-1)]
                good=[(2*s*(p-1),j-2*s*(p-1)) for s in range(0,k+1) if 0<=j-2*s*(p-1)<=2*kk*(p-1)]
                ok(sorted(surv)==sorted(good),f"pairs p={p} k={k} k'={kk} i={i}: {surv} vs {good}")
                # and no surviving odd-odd pair
                ok(all(a%2==0 for a,_ in surv),f"odd pair p={p}")
    # the pairs survive only with V: without V (all even a) there are extra pairs for k,k'>=1 at p>=3
    # control: k=k'=1, i=1 (index 2(p-1)); without V every even a in [0,2(p-1)] pairs (p pairs), with V only 2
    k=kk=1; i=1; j=2*(k+kk-i)*(p-1)
    extra=[(a,j-a) for a in range(0,j+1,2) if a<=2*k*(p-1) and j-a<=2*kk*(p-1)]
    ok(len(extra)==p and p>2,f"V needed p={p}: {len(extra)} pairs without V")
print(f"checks={checks} fails={fails}")
