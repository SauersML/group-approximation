# rank-based rectangle profile Lambda^ = max_{s,t<=W} rank([b^s,c^t]-I)/(s+t) for b=+1 on Z/n
import numpy as np
def ncyc(w):
    n=len(w); seen=np.zeros(n,bool); k=0
    for x in range(n):
        if not seen[x]:
            k+=1; y=x
            while not seen[y]: seen[y]=True; y=w[y]
    return k
def rankprof(c,W):
    c=np.asarray(c); n=len(c); x=np.arange(n); ci=np.argsort(c); best=0.0; arg=None
    ct=x.copy(); cti=x.copy()
    for t in range(1,W+1):
        ct=c[ct]; cti=ci[cti]
        for s in range(1,W+1):
            if n/(s+t)<=best: break
            # w = b^s c^t b^-s c^-t  (apply right to left)
            w=(ct[(cti-s)%n]+s)%n
            r=n-ncyc(w); v=r/(s+t)
            if v>best: best,arg=v,(s,t,r)
    return best,arg
