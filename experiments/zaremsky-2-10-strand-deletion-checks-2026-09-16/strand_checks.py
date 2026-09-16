# Referee sanity checks for the strand-deletion identities (D1)-(D4) of
# research/artifacts/braided-v-continuum-normal-subgroups-2026-09-16.md.
# Braids are words in sigma_i^{+-1}. 3-strand equalities (D1, D2, D3, commutators on degenerate triples) are
# decided by the unreduced Burau representation, which is faithful on B_3; the n-strand left-inverse check (D4)
# uses the faithful Artin action on F_n with short words. Referee replay 2026-09-16: 150 random trials, n = 3..5,
# output 'failures = 0; commutators with nontrivial 3-strand projection: 90'.
import random
random.seed(20260916)

def red(w):
    out=[]
    for x in w:
        if out and out[-1]==-x: out.pop()
        else: out.append(x)
    return out
def inv(w): return [-x for x in reversed(w)]

def artin(word,n):
    # images of generators x_1..x_n (letters +-j) under composite automorphism, acting letter by letter
    img={j:[j] for j in range(1,n+1)}
    for e in word:
        i=abs(e)
        if e>0: sub={i:[i,i+1,-i], i+1:[i]}
        else:   sub={i:[i+1], i+1:[-(i+1),i,i+1]}
        def app(w):
            r=[]
            for x in w:
                j=abs(x)
                s=sub.get(j,[j])
                r.extend(s if x>0 else inv(s))
            return red(r)
        img={j:app(img[j]) for j in img}
    return img
def equal(w1,w2,n): return artin(w1,n)==artin(w2,n)
def trivial(w,n): return artin(w,n)=={j:[j] for j in range(1,n+1)}

def perm(word,n):
    lab=list(range(1,n+1))
    for e in word:
        i=abs(e); lab[i-1],lab[i]=lab[i],lab[i-1]
    return lab
def delete(word,n,keep):  # keep = set of strand labels (= starting positions)
    lab=list(range(1,n+1)); out=[]
    for e in word:
        i=abs(e)
        if lab[i-1] in keep and lab[i] in keep:
            ip=sum(1 for q in range(i-1) if lab[q] in keep)+1
            out.append(ip if e>0 else -ip)
        lab[i-1],lab[i]=lab[i],lab[i-1]
    return out
def clone(word,n,k):  # clone strand starting at position k into k,k+1
    lab=list(range(1,n+1)); out=[]
    for e in word:
        i=abs(e); s=1 if e>0 else -1
        j=lab.index(k)+1
        newpos=lambda q: q if q<j else q+1
        if lab[i-1]==k:   out += [s*(i+1), s*i]
        elif lab[i]==k:   out += [s*i, s*(i+1)]
        else:             out.append(s*newpos(i))
        lab[i-1],lab[i]=lab[i],lab[i-1]
    return out
def A(i,j):
    up=list(range(j-1,i,-1))
    return up+[i,i]+[-x for x in reversed(up)]
def rand_pure(n,L):
    w=[]
    for _ in range(L):
        i=random.randrange(1,n); j=random.randrange(i+1,n+1)
        a=A(i,j); w+= a if random.random()<.5 else inv(a)
    return w
def rand_braid(n,L): return [random.choice([1,-1])*random.randrange(1,n) for _ in range(L)]
def comm(a,b): return a+b+inv(a)+inv(b)


# unreduced Burau representation, polynomial entries as dict exp->coef; faithful on B_3 (and B_2)
from functools import reduce
def padd(a,b):
    r=dict(a)
    for k,v in b.items():
        r[k]=r.get(k,0)+v
        if r[k]==0: del r[k]
    return r
def pmul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            r[k1+k2]=r.get(k1+k2,0)+v1*v2
    return {k:v for k,v in r.items() if v}
def mmul(A,B,n):
    return [[reduce(padd,[pmul(A[i][l],B[l][j]) for l in range(n)],{}) for j in range(n)] for i in range(n)]
def gen(e,n):
    i=abs(e)-1
    M=[[({0:1} if r==c else {}) for c in range(n)] for r in range(n)]
    if e>0:
        M[i][i]={0:1,1:-1}; M[i][i+1]={1:1}; M[i+1][i]={0:1}; M[i+1][i+1]={}
    else:
        M[i][i]={}; M[i][i+1]={0:1}; M[i+1][i]={-1:1}; M[i+1][i+1]={0:1,-1:-1}
    return M
def burau(word,n):
    M=[[({0:1} if r==c else {}) for c in range(n)] for r in range(n)]
    for e in word: M=mmul(M,gen(e,n),n)
    return M

fails=0
nontriv=0
I3=burau([],3)
# Burau sanity: braid relation, inverse, and non-triviality of a commutator in PB_3
assert burau([1,-1],3)==I3 and burau([-2,2],3)==I3
assert burau([1,2,1],3)==burau([2,1,2],3)
assert burau(comm(A(1,2),A(1,3)),3)!=I3

for trial in range(150):
    n=random.randint(3,5)
    p=rand_pure(n,4); pshort=rand_pure(n,2); assert perm(p,n)==list(range(1,n+1))
    k=random.randint(1,n)
    q=clone(p,n,k); assert perm(q,n+1)==list(range(1,n+2))
    # (D4) delete clone k+1
    qs=clone(pshort,n,k)
    if not equal(delete(qs,n+1,set(range(1,n+2))-{k+1}),pshort,n): fails+=1; print('D4 fail')
    # (D2) generic triples
    for _ in range(3):
        S=sorted(random.sample(range(1,n+1),3))
        Sk={i if i<=k else i+1 for i in S}
        if not burau(delete(q,n+1,Sk),3)==burau(delete(p,n,set(S)),3): fails+=1; print('D2 fail')
    # (D3) degenerate triples: factors through pi_{k,j}
    jp=random.choice([x for x in range(1,n+2) if x not in (k,k+1)])
    j=jp if jp<k else jp-1
    lhs=delete(q,n+1,{k,k+1,jp})
    two=delete(p,n,{k,j}); kpp=1 if k<j else 2
    if not burau(lhs,3)==burau(clone(two,2,kpp),3): fails+=1; print('D3 fail')
    # commutators die on degenerate triples
    p2=rand_pure(n,3); c=comm(p,p2); qc=clone(c,n,k)
    if not burau(delete(qc,n+1,{k,k+1,jp}),3)==burau([],3): fails+=1; print('D3-commutator fail')
    # (D1) conjugation: pi_S(b c b^-1) = beta pi_{S1}(c) beta^-1
    b=rand_braid(n,6); w=b+c+inv(b)
    S=set(random.sample(range(1,n+1),3))
    # strands ending at positions S: labels at end of b c b^-1 -- pure, so labels S. Through c they sit at positions S1
    lab=perm(b,n)  # after b (applied first as letters), lab[pos-1]=label
    # w = b . c . b^-1 as words applied left to right; the strand labelled s is at position lab.index(s)+1 inside c
    S1={lab.index(s)+1 for s in S}
    beta=delete(b,n,S)
    if not burau(delete(w,n,S),3)==burau(beta+delete(c,n,S1)+inv(beta),3): fails+=1; print('D1 fail')
    # sanity: clones of nontrivial commutators are nontrivial
    nontriv += (burau(delete(c,n,S1),3)!=burau([],3))
print('trials done, failures =',fails,'; commutators with nontrivial 3-strand projection:',nontriv)
