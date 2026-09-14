# Exact census of nonsingular t-shapes (cyclic words in t, t^-1) by length,
# classified by the Forester--Rourke definitions (arXiv:math/0306088, pi-two.tex l.367-385):
#   D(T): delete all subwords t t^-1 (cyclically) and close up
#   complexity: min m with D^m(T) = t^q ; root: D^(m-1)(T)
#   clump: maximal connected subsequence t^q or t^-q with q > 1 (cyclic)
#   one-clump: exactly one clump, and it is not the whole shape
#   amenable: root is t t^-1 or a one-clump shape
import itertools, json, sys
def canon(s):
    n=len(s); rots=[tuple(s[i:]+s[:i]) for i in range(n)]
    inv=tuple(-x for x in reversed(s)); rots+= [tuple(inv[i:]+inv[:i]) for i in range(n)]
    return min(rots)
def D(s):
    n=len(s); dele=[False]*n
    for i in range(n):
        if s[i]==1 and s[(i+1)%n]==-1: dele[i]=True; dele[(i+1)%n]=True
    return [x for x,d in zip(s,dele) if not d]
def pure(s): return len(s)>0 and (all(x==1 for x in s) or all(x==-1 for x in s))
def root(s):
    if pure(s): return None
    prev=s; cur=D(s)
    while not pure(cur):
        prev=cur; cur=D(cur)
    return prev
def clumps(s):
    n=len(s)
    if pure(s): return [n]
    i0=next(i for i in range(n) if s[i]!=s[i-1])
    runs=[]; cur=1
    for j in range(1,n+1):
        a=s[(i0+j-1)%n]; b=s[(i0+j)%n]
        if j<n and b==a: cur+=1
        else: runs.append(cur); cur=1
    return [r for r in runs if r>1]
def one_clump(s):
    c=clumps(s); return len(c)==1 and c[0]<len(s)
def amenable(s):
    r=root(s)
    if r is None: return False
    return (len(r)==2 and sum(r)==0) or one_clump(r)
def proper_power(s):
    n=len(s)
    return any(n%d==0 and d<n and s==s[d:]+s[:d] for d in range(1,n))
out={}
for L in range(1,int(sys.argv[1])+1):
    seen=set(); rows=[]
    for s in itertools.product((1,-1),repeat=L):
        s=list(s)
        if sum(s)==0: continue
        c=canon(s)
        if c in seen: continue
        seen.add(c); c=list(c)
        kind="levin" if pure(c) else ("amenable" if amenable(c) else "nonamenable")
        rows.append(("".join("+" if x==1 else "-" for x in c),sum(c),kind,proper_power(c),"".join("+" if x==1 else "-" for x in (root(c) or [])),len(clumps(root(c))) if root(c) else None))
    out[L]=rows
    na=[r for r in rows if r[2]=="nonamenable"]
    print("L=%d nonsingular=%d levin=%d amenable=%d nonamenable=%d (proper powers %d)"%(L,len(rows),sum(r[2]=="levin" for r in rows),sum(r[2]=="amenable" for r in rows),len(na),sum(r[3] for r in na)))
    if L<=12:
        for r in na: print("   ",r)
json.dump({str(k):v for k,v in out.items()},open("shape_census.json","w"))
# sanity checks against the pinned statements
assert amenable([1,1,1,-1])            # t t t t^-1 amenable (FR example, exponent 2)
for L in range(1,11):
    for s in itertools.product((1,-1),repeat=L):
        s=list(s)
        if abs(sum(s))==1 and not pure(s): assert amenable(s), s          # FR l.382-383
        if proper_power(s) and sum(s)!=0 and not pure(s): assert not amenable(s), s   # FR l.384-385
print("ASSERTS_OK")
