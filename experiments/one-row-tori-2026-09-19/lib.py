import numpy as np
def arcx(n, th, al, be, ga):
    x=np.arange(n); c=np.empty(n,dtype=np.int64)
    A=x<al; B=(x>=al)&(x<al+be); C=x>=al+be
    c[A]=x[A]+th; c[B]=x[B]+th+ga; c[C]=x[C]+th-be
    return c%n
def breaks(ct):
    n=len(ct); x=np.arange(n)
    return np.nonzero(ct[(x+1)%n]!=(ct+1)%n)[0]
def profile(c,S,T):
    n=len(c); x=np.arange(n); best=0; arg=None; ct=x.copy()
    for t in range(1,T+1):
        ct=c[ct]
        for s in range(1,S+1):
            m=int(np.count_nonzero(ct[(x+s)%n]!=(ct+s)%n)); v=m/(s+t)
            if v>best: best,arg=v,(s,t,m)
    return best,arg
def vsaddles(c):
    # vertical saddle connections: chains of positions y -> c(y) while y not a break
    n=len(c); B1=set(breaks(c).tolist()); ci=np.argsort(c); Bm=set(breaks(ci).tolist())
    out=[]
    for y0 in sorted(Bm):
        y=y0; L=1
        while y not in B1: y=int(c[y]); L+=1
        out.append((y0,y,L))
    return out
