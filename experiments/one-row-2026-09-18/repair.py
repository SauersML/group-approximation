import numpy as np, itertools
from collections import Counter
def rot_cost(c, members, ins):
    """members: list of row-points in cyclic order forming one new b-cycle (subset of Z/n);
    ins: dict position-> block size (>0 insert before that point, <0 delete that many points starting there).
    Returns cost of c' = rotation on the new cycle, counting c-mismatches among members mapped inside."""
    pts=[]; dele=0; extra=0
    skip=0
    for x in members:
        k=ins.get(x,0)
        if k>0: extra+=k; pts.extend([None]*k)
        if k<0: skip=-k
        if skip>0: skip-=1; dele+=1; continue
        pts.append(x)
    L=len(pts)
    if L==0: return 10**9
    pos={x:i for i,x in enumerate(pts) if x is not None}
    cnt=Counter()
    for x,i in pos.items():
        y=c[x]
        if y in pos: cnt[(pos[y]-i)%L]+=1
    good=max(cnt.values()) if cnt else 0
    return (len(pos)-good) + extra + dele
def best_repair(c, cand, M):
    n=len(c); members=list(range(n)); best=(10**9,None)
    for k in range(-M,M+1):
        for p in cand:
            v=rot_cost(c,members,{p:k})+(2 if k else 0)
            if v<best[0]: best=(v,('one',p,k))
    for p,q in itertools.combinations(sorted(set(cand)),2):
        for k in range(-M,M+1):
            for l in range(-M,M+1):
                if k==0 or l==0: continue
                v=rot_cost(c,members,{p:k,q:l})+4
                if v<best[0]: best=(v,('two',p,k,q,l))
    # two-cycle cut at two candidate positions
    for p,q in itertools.combinations(sorted(set(cand)),2):
        A=list(range(p,q)); B=list(range(q,n))+list(range(0,p))
        v=rot_cost(c,A,{})+rot_cost(c,B,{})+4
        # c-mismatch counted inside each cycle only; points crossing counted as bad already
        if v<best[0]: best=(v,('cut',p,q))
    return best
