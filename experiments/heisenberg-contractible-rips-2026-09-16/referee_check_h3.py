#!/usr/bin/env python3
"""Referee cross-check (2026-09-16), written independently of search_h3_rips.py.

Recomputes (L1)-(L3) for S = {x,y,z,xz,yz,xy,xyz}^+-1, checks that 3000 random
integer directions avoiding cone boundaries each lie in exactly one open cone (L4),
and, as a GLOBAL sanity check not used in the proof, that 300 random rational points
of [0,1]^3 each lie in exactly one tetrahedron g.tau (g in a box of H, tau a
tetrahedron at 1), with tetrahedra realized affinely in H_3(R) = R^3.
"""
from fractions import Fraction as F
import itertools, random
def mul(g,h): return (g[0]+h[0],g[1]+h[1],g[2]+h[2]+g[0]*h[1])
def inv(g): return (-g[0],-g[1],-g[2]+g[0]*g[1])
Sp=[(1,0,0),(0,1,0),(0,0,1),(1,0,1),(0,1,1),(1,1,1),(1,1,2)]
S=set(Sp)|{inv(s) for s in Sp}; assert len(S)==14
Sl=sorted(S)
adj={s:{t for t in Sl if t!=s and mul(inv(s),t) in S} for s in Sl}
E=[(s,t) for s in Sl for t in adj[s] if s<t]
T=[c for c in itertools.combinations(Sl,3) if c[1] in adj[c[0]] and c[2] in adj[c[0]] and c[2] in adj[c[1]]]
Q=[c for c in itertools.combinations(Sl,4) if all(b in adj[a] for a,b in itertools.combinations(c,2))]
print("V E F Q",len(Sl),len(E),len(T),len(Q))
def det(a,b,c): return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
assert all(abs(det(*t))==1 for t in T)
for e in E:
    opp=[ [v for v in t if v not in e][0] for t in T if e[0] in t and e[1] in t]
    assert len(opp)==2, e
    assert det(e[0],e[1],opp[0])*det(e[0],e[1],opp[1])<0
for v in Sl:
    lk=[[w for w in t if w!=v] for t in T if v in t]
    # single cycle
    nb={}
    for a,b in lk: nb.setdefault(a,[]).append(b); nb.setdefault(b,[]).append(a)
    assert all(len(x)==2 for x in nb.values())
    start=lk[0][0]; prev=None; cur=start; seen=set()
    while cur not in seen:
        seen.add(cur); nxt=[x for x in nb[cur] if x!=prev][0] if prev is not None else nb[cur][0]; prev,cur=cur,nxt
    assert len(seen)==len(nb)
print("chi",len(Sl)-len(E)+len(T))
# ray counts over random integer directions: count cones containing direction strictly
def solve(t,v):
    # v = x a + y b + z c ; Cramer
    a,b,c=t; D=det(a,b,c)
    return (F(det(v,b,c),D),F(det(a,v,c),D),F(det(a,b,v),D))
random.seed(1); counts=set()
for _ in range(3000):
    v=tuple(random.randint(-10**6,10**6) for _ in range(3))
    k=0;bd=False
    for t in T:
        co=solve(t,v)
        if min(co)>0: k+=1
        elif min(co)==0 and max(co)>0 and all(x>=0 for x in co): bd=True
    if not bd: counts.add(k)
print("ray counts",counts)
# global: tetrahedra orbits at 1, check points in [0,1)^3 covered exactly once
tets=[((0,0,0),)+t for t in T]
# generate translates g*tet for g in a box; count containment of random rational points
def contains(tet,p):
    o=tet[0]; vs=[tuple(x-y for x,y in zip(w,o)) for w in tet[1:]]
    q=tuple(x-y for x,y in zip(p,o))
    co=solve(vs,q); return min(co)>=0 and sum(co)<=1, (min(co)==0 or sum(co)==1)
allt=[]
for g in itertools.product(range(-3,4),range(-3,4),range(-6,7)):
    for t in tets: allt.append(tuple(mul(g,w) for w in t))
allt=list({tuple(sorted(t)) for t in allt})
bad=0
for _ in range(300):
    p=tuple(F(random.randint(0,10**6),10**6) for _ in range(3))
    k=0
    for t in allt:
        if not all(min(w[i] for w in t)<=p[i]<=max(w[i] for w in t) for i in range(3)): continue
        c,b=contains(t,p)
        if c: k+=1
    if k!=1: bad+=1
print("points not covered exactly once:",bad, "tets",len(allt))
