"""Whitehead minimization in a free group F_r (letters 1..r, inverses negative).
A cyclic word is primitive iff its Whitehead-minimal cyclic length is 1."""
import itertools
def fr(w):
    o=[]
    for x in w:
        if o and o[-1]==-x: o.pop()
        else: o.append(x)
    return o
def cr(w):
    w=fr(w); i,j=0,len(w)-1
    while i<j and w[i]==-w[j]: i+=1; j-=1
    return w[i:j+1]
def wh_auts(r):
    L=[x for i in range(1,r+1) for x in (i,-i)]
    for a in L:
        rest=[x for x in L if x not in (a,-a)]
        for bits in itertools.product((0,1),repeat=len(rest)):
            S=set(x for x,b in zip(rest,bits) if b)
            if not S: continue
            yield a,S
def apply(w,a,S):
    # x -> (a^-1 if x^-1... standard: x -> a^{[x^-1 in S]}? use: x -> x a if x in S ; x -> a^-1 x if x^-1 in S
    o=[]
    for x in w:
        if x in (a,-a): o.append(x); continue
        pre = [-a] if (-x) in S else []
        post = [a] if x in S else []
        o.extend(pre+[x]+post)
    return cr(o)
def wh_min(w,r):
    w=cr(w); improved=True
    auts=list(wh_auts(r))
    while improved:
        improved=False
        for a,S in auts:
            v=apply(w,a,S)
            if len(v)<len(w): w=v; improved=True; break
    return w
