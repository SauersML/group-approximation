#!/usr/bin/env python3
"""Random search: random w in [F,F] (not a proper power), random vertex identifications among two w-circles,
fold, keep connected graphs with two distinct lifts, tabulate the dependency type of ([u0],[u1]).
Usage: rand3.py NGEN MINLEN MAXLEN TRIALS SEED"""
import sys, random, collections
from search import classes, ratio
def randw(rng, ngen, L):
    while True:
        w=[]
        while len(w)<L:
            l=(rng.randrange(ngen), rng.choice((1,-1)))
            if w and l==(w[-1][0],-w[-1][1]): continue
            w.append(l)
        if w[0]==(w[-1][0],-w[-1][1]): continue
        if any(sum(s for g,s in w if g==h) for h in range(ngen)): continue
        if any(L%d==0 and w==w[d:]+w[:d] for d in range(1,L)): continue
        if len({g for g,s in w})<ngen: continue
        return tuple(w)
ngen,m,M,T,seed=map(int,sys.argv[1:6]); rng=random.Random(seed)
st=collections.Counter(); ex={}
for t in range(T):
    L=rng.randrange(m,M+1,2); w=randw(rng,ngen,L)
    k=rng.randrange(1,7)
    idents=[(rng.randrange(2*L),rng.randrange(2*L)) for _ in range(k)]
    res=classes(w,idents)
    if res is None: st['none']+=1; continue
    r,(v0,v1)=res
    rt=ratio(v0,v1)
    key='indep' if rt is None else str(rt)
    st[key]+=1
    if key not in ex and key!='indep': ex[key]=(''.join(('xyz'[g] if s==1 else 'XYZ'[g]) for g,s in w),idents,r,v0,v1)
print(st.most_common(30))
for k,v in ex.items(): print(k,v)
