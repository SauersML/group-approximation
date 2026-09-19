import numpy as np
from excrep import induced
def exm(c,M):
    n=len(c); x=np.arange(n); C=np.array(c)
    conj=[(C[(x+p)%n]-p)%n for p in range(n)]
    for m in range(1,M+1):
        for r in range(1,n+m):
            d=induced(n+m,r,m)
            for cp in conj:
                if cp[0]==d[0] and np.array_equal(cp,d): return m,r
    return None
