# Laurent polynomial matrices over Z (or rationals) as dicts
from fractions import Fraction
import itertools, sys
def padd(p,q):
    r=dict(p)
    for e,c in q.items():
        r[e]=r.get(e,0)+c
        if r[e]==0: del r[e]
    return r
def pmul(p,q):
    r={}
    for e1,c1 in p.items():
        for e2,c2 in q.items():
            e=e1+e2; r[e]=r.get(e,0)+c1*c2
    return {e:c for e,c in r.items() if c!=0}
def mmul(A,B):
    n=len(A); m=len(B[0]); l=len(B)
    C=[[{} for _ in range(m)] for _ in range(n)]
    for i in range(n):
        for j in range(m):
            acc={}
            for k in range(l):
                if A[i][k] and B[k][j]:
                    acc=padd(acc,pmul(A[i][k],B[k][j]))
            C[i][j]=acc
    return C
def deg(p): return max(p) if p else None
def P(*terms):  # P((e,c),...)
    d={}
    for e,c in terms: d[e]=d.get(e,0)+c
    return {e:c for e,c in d.items() if c!=0}
# f, k and inverses over Z[t,t^-1]
f=[[P((1,1)),{},{}],[{},P((0,1)),{}],[{},{},P((-1,1))]]
fi=[[P((-1,1)),{},{}],[{},P((0,1)),{}],[{},{},P((1,1))]]
k=[[{},P((0,-1),(1,-1)),P((-1,-1),(0,-1),(1,-1))],[{},P((-1,1),(0,1),(1,1)),P((-2,1),(-1,1),(0,1),(1,1))],[P((0,1)),{},{}]]
def minors2(M):
    out=[]
    for r in itertools.combinations(range(3),2):
        for c in itertools.combinations(range(3),2):
            m=padd(pmul(M[r[0]][c[0]],M[r[1]][c[1]]), {e:-v for e,v in pmul(M[r[0]][c[1]],M[r[1]][c[0]]).items()})
            out.append(m)
    return out
def cartan(M):
    l1=max(deg(p) for row in M for p in row if p)
    l12=max(deg(p) for p in minors2(M) if p)
    return (l1, l12-l1, -l12)
def ident(): return [[P((0,1)) if i==j else {} for j in range(3)] for i in range(3)]
def inv3(M):
    # adjugate (det=1 assumed)
    adj=[[None]*3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            r=[x for x in range(3) if x!=j]; c=[x for x in range(3) if x!=i]
            m=padd(pmul(M[r[0]][c[0]],M[r[1]][c[1]]), {e:-v for e,v in pmul(M[r[0]][c[1]],M[r[1]][c[0]]).items()})
            if (i+j)%2: m={e:-v for e,v in m.items()}
            adj[i][j]=m
    return adj
ki=inv3(k)
assert mmul(k,ki)==ident(), 'k inverse check'
assert mmul(f,fi)==ident()
