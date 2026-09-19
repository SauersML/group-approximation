import numpy as np
def arcx(n, th, al, be, ga):
    # circle 3-arc exchange: A=[0,al),B=[al,al+be),C=[al+be,n); c = R_th o swap(B,C)
    assert al+be+ga==n
    x=np.arange(n); c=np.empty(n,dtype=np.int64)
    A=x<al; B=(x>=al)&(x<al+be); C=x>=al+be
    c[A]=x[A]+th; c[B]=x[B]+th+ga; c[C]=x[C]+th-be
    c%=n; assert len(set(c.tolist()))==n
    return c
def profile(c, S, T):
    n=len(c); x=np.arange(n); best=0; arg=None; ct=x.copy()
    for t in range(1,T+1):
        ct=c[ct]
        for s in range(1,S+1):
            # [b^s,c^t] moved iff c^t(x+s) != c^t(x)+s
            m=int(np.count_nonzero(ct[(x+s)%n]!=(ct+s)%n))
            v=m/(s+t)
            if v>best: best=v; arg=(s,t,m)
    return best,arg
