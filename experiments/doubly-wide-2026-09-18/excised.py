import numpy as np
def excised(W,a,k):
    """one-row torus Z/W, b=+1, c=+a, with squares 0..k-1 excised (b,c skip them)."""
    keep=list(range(k,W)); idx={x:i for i,x in enumerate(keep)}; n=len(keep)
    b=np.zeros(n,int); c=np.zeros(n,int)
    for x in keep:
        y=(x+1)%W
        while y<k: y=(y+1)%W
        b[idx[x]]=idx[y]
        y=(x+a)%W
        while y<k: y=(y+a)%W
        c[idx[x]]=idx[y]
    assert len(set(b))==n and len(set(c))==n
    return b,c
