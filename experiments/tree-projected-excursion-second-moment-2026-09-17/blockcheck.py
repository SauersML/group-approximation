"""Brute-force check of the one-block lumped bounds on concrete decorations of F_2 x Z."""
from criterion import *
import random
def inv(l): return l[0]+('-' if len(l)==1 else '')
def mul(w,l):
    if w and w[-1]==inv(l): return w[:-1]
    return w+(l,)
def dec(D,l):
    return D[l[0]] if len(l)==1 else [-d for d in D[l[0]]]
def step(vx,l,d): return (mul(vx[0],l), vx[1]+d)
def block_paths(D,base):
    # base vertex in fibre w = ('a',), previous letter a, next letter b
    prev='a'; t='b'; res=[]
    letters=['a','a-','b','b-']
    for s in dec(D,t):
        nxt=step(base,t,s); res.append(([frozenset((base,nxt))],nxt))
    for e in letters:
        if e==inv(prev): continue
        De=dec(D,e)
        for u in De:
            for u2 in De:
                if u==u2: continue
                y=step(base,e,u); plus=step(y,inv(e),-u2)
                for s in dec(D,t):
                    if e==t and s==u2: continue
                    nxt=step(plus,t,s)
                    E=[frozenset((base,y)),frozenset((y,plus)),frozenset((plus,nxt))]
                    assert len(set(E))==3
                    res.append((E,nxt))
    return res
def check(D,m,p,TE,hs):
    x=1/p
    T=matrix(TE,m,p)
    base0=(('a',),0)
    P0=block_paths(D,base0)
    worst=[[F(0)]*2 for _ in range(2)]
    for h in hs:
        P1=block_paths(D,(('a',),h))
        to=[F(0),F(0)]
        for E1,n1 in P0:
            for E2,n2 in P1:
                sh=len(set(E1)&set(E2))
                wgt=p**(len(E1)+len(E2))*x**sh
                to[0 if n1==n2 else 1]+=wgt
        st=0 if h==0 else 1
        for k in range(2): worst[st][k]=max(worst[st][k],to[k])
    return worst,T
random.seed(1)
TE=terms(3,True)
for trial in range(6):
    m=random.choice([3,4])
    D={'a':sorted(random.sample(range(0,6),m)),'b':sorted(random.sample(range(0,6),m))}
    p=F(1,10)
    worst,T=check(D,m,p,TE,range(-12,13))
    ok=all(worst[i][j]<=T[i][j] for i in range(2) for j in range(2))
    print(D,ok,[[float(a) for a in r] for r in worst],[[float(a) for a in r] for r in T])
