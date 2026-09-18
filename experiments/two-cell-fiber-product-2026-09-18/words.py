# Direct word search: read cyclically reduced w from v0 and v1 in a folded graph; report z1 = lam z0 != 0.
import sys
from fractions import Fraction as Fr
edges=[(0,0,0),(1,2,0),(0,1,1),(1,0,1),(2,2,1)]
def step(v,l):  # l in 0,1 (x,y), 2,3 (X,Y inverses)
    s=l%2
    for i,(a,b,m) in enumerate(edges):
        if m!=s: continue
        if l<2 and a==v: return b,i,1
        if l>=2 and b==v: return a,i,-1
    return None
def read(v,w):
    z=[0]*len(edges)
    for l in w:
        r=step(v,l)
        if r is None: return None
        v,i,sg=r; z[i]+=sg
    return v,z
def pp(w):
    n=len(w)
    return any(n%d==0 and w==w[:d]*(n//d) for d in range(1,n))
L=int(sys.argv[1]); v0,v1=0,1
out=0
def rec(w):
    global out
    if w and (read(v0,w) is None or read(v1,w) is None): return
    if w and len(w)>=4 and (w[0]-w[-1])%4!=2 and not pp(w):
        a=read(v0,w); b=read(v1,w)
        if a and b and a[0]==v0 and b[0]==v1 and any(a[1]):
            for lam in (Fr(2),Fr(1,2),Fr(3,2),Fr(2,3)):
                if all(y==lam*x for x,y in zip(a[1],b[1])):
                    print(''.join('xyXY'[c] for c in w),lam,a[1],b[1]); out+=1
    if len(w)==L or out>10: return
    for l in range(4):
        if w and (l-w[-1])%4==2: continue
        rec(w+[l])
rec([])
