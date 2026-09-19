import numpy as np
from scipy.optimize import linear_sum_assignment
def cycles(p):
    n=len(p); seen=[False]*n; out=[]
    for i in range(n):
        if not seen[i]:
            cyc=[]; j=i
            while not seen[j]: seen[j]=True; cyc.append(j); j=p[j]
            out.append(cyc)
    return out
def onesided(b,c):
    """min #{x: c'(x)!=c(x)} over c' commuting with b (b fixed)."""
    rows=cycles(b); pos={}
    for r,cyc in enumerate(rows):
        for i,x in enumerate(cyc): pos[x]=(r,i)
    bylen={}
    for r,cyc in enumerate(rows): bylen.setdefault(len(cyc),[]).append(r)
    total=0
    for L,rs in bylen.items():
        idx={r:i for i,r in enumerate(rs)}
        wt=np.zeros((len(rs),len(rs)))
        for r in rs:
            cnt={}
            for i,x in enumerate(rows[r]):
                r2,i2=pos[c[x]]
                if r2 in idx: cnt[(r2,(i2-i)%L)]=cnt.get((r2,(i2-i)%L),0)+1
            for (r2,e),v in cnt.items(): wt[idx[r],idx[r2]]=max(wt[idx[r],idx[r2]],v)
        ri,ci=linear_sum_assignment(-wt)
        total+=L*len(rs)-wt[ri,ci].sum()
    return int(total)
def cylinders(b,c):
    """horizontal cylinders: list of (width,height); tori excluded."""
    rows=cycles(b); pos={}
    for r,cyc in enumerate(rows):
        for x in cyc: pos[x]=r
    def equiv(r):
        return all(c[b[x]]==b[c[x]] for x in rows[r])
    nxt={r:pos[c[rows[r][0]]] for r in range(len(rows)) if equiv(r)}
    hasprev=set(nxt.values()); out=[]
    for r in range(len(rows)):
        if r in hasprev: continue
        h=1; s=r
        while s in nxt: s=nxt[s]; h+=1
        out.append((len(rows[r]),h))
    return out
