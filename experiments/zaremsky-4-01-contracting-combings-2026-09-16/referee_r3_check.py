#!/usr/bin/env python3
# Referee check (2026-09-16), evidence only. Run: timeout 600 python3 referee_r3_check.py
# independent referee check: G = Z^3 x| C_3 (cyclic coordinate permutation), elements (t,k)
# acting v -> P^k v + t. S = {g != 1 : |t|_inf <= 1}. BFS metric vs formula; clamp combing contracting.
import itertools
def P(v,k):
    for _ in range(k%3): v=(v[2],v[0],v[1])
    return v
def Pinv(v,k): return P(v,(-k)%3)
def mul(g,h):
    t,k=g; u,l=h; pu=P(u,k); return (tuple(a+b for a,b in zip(t,pu)),(k+l)%3)
def inv(g):
    t,k=g; return (tuple(-x for x in Pinv(t,k)),(-k)%3)
one=((0,0,0),0)
S=[(t,k) for t in itertools.product((-1,0,1),repeat=3) for k in range(3) if (t,k)!=one]
L=4
dist={one:0}; fr=[one]
for i in range(1,L+1):
    nx=[]
    for g in fr:
        for s in S:
            h=mul(g,s)
            if h not in dist: dist[h]=i; nx.append(h)
    fr=nx
bad=0
for g,k in dist.items():
    want=0 if g==one else max(max(abs(x) for x in g[0]),1)
    if want!=k: bad+=1
print("metric mismatches",bad,len(dist))
def norm(t): return max(abs(x) for x in t)
def d(g,h):
    if g==h: return 0
    t=mul(inv(g),h)[0]; return max(norm(t),1)
cl=lambda v,r: tuple(max(-r,min(r,x)) for x in v)
def comb(g,n):
    if n==0: return one
    if n>=norm(g[0]): return g
    return (cl(g[0],n),0)
R=2
win=[(t,k) for t in itertools.product(range(-R,R+1),repeat=3) for k in range(3)]
T=R+2
paths={g:[comb(g,n) for n in range(T+1)] for g in win}
fails=0; checks=0
for g in win:
    for n in range(T): assert d(paths[g][n],paths[g][n+1])<=1
for C in (2,3,4):
    c=C//2
    for g in win:
        pg=paths[g]
        for h in win:
            ph=paths[h]
            for n in range(c,T+1):
                for n2 in range(n+1):
                    checks+=1
                    if d(pg[n],ph[n2])<=C and d(pg[n-c],ph[n2])>C: fails+=1
print("checks",checks,"fails",fails)
