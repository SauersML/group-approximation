#!/usr/bin/env python3
"""Float, per decoration: exact per-offset transfer radius (anal.rho, pairx.c block sums) and
its 4-class lumping (lump.py), both over 3 w^2, at p*(m,2), for the near-AP chi = 2 decoration
and random rigid decorations. usage: python3 exact9.py m N  (needs ./pairx in cwd)"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), '..', 'tree-projected-pollard-slot-second-moment-2026-09-18'))
import sys, subprocess, random, anal, lump, os
from math import sqrt
def pstar(m, v=2):
    d = 4*m+v; la = v+2*sqrt(3)*m
    return 2/(la+sqrt(la*la-4*(d-1)))
def norm(X):
    a=min(X); return tuple(sorted(x-a for x in X))
def rigid(A,B):
    return len({norm(A),norm([-x for x in A]),norm(B),norm([-x for x in B])})==4
def run(A,B,c,p,tag):
    fn='ex_%d.txt'%os.getpid()
    with open(fn,'w') as f:
        subprocess.run(['./pairx',str(c),'-1,0,1',str(len(A))]+list(map(str,A))+[str(len(B))]+list(map(str,B)),stdout=f,check=True)
    ctx=anal.load(fn)
    up,low,w=anal.rho(ctx,p,300)
    T,w2=lump.lumped_T(ctx,p,c)
    import engine_p as E
    L=3*w2; Tn=[[a/L for a in r] for r in T]
    lam,_=E.rho_phi(Tn,1,300)
    os.remove(fn)
    print('%-10s c=%d A=%s B=%s exact_up %.5f low %.5f lumped %.5f'%(tag,c,A,B,up,low,lam),flush=True)
m=int(sys.argv[1]); p=pstar(m)
print('m',m,'p*',p)
A=list(range(m-1))+[m]; B=list(range(m-2))+[m-1,m]
for c in (1,2,5): run(A,B,c,p,'nearAP')
rng=random.Random(7)
for i in range(int(sys.argv[2])):
    while True:
        W=int(rng.choice([1.3,2,3,6])*m)
        A=sorted(rng.sample(range(W),m)); B=sorted(rng.sample(range(W),m))
        if rigid(A,B): break
    run(A,B,rng.choice([1,2,3,7,50]),p,'rand%d'%i)
