import numpy as np
def rank_comm(b,c,s,t):
    n=len(b); bs=np.arange(n); ct=np.arange(n)
    for _ in range(s): bs=b[bs]
    for _ in range(t): ct=c[ct]
    # P = b^s c^t b^-s c^-t ; rank(P-I)= n - #cycles
    inv=lambda p: np.argsort(p)
    P=bs[ct[inv(bs)[inv(ct)]]]
    seen=np.zeros(n,bool); cyc=0
    for i in range(n):
        if not seen[i]:
            cyc+=1; j=i
            while not seen[j]: seen[j]=True; j=P[j]
    return n-cyc
def profile(b,c,M):
    best=0;arg=None
    for s in range(1,M+1):
        for t in range(1,M+1):
            r=rank_comm(b,c,s,t)/(s+t)
            if r>best: best,arg=r,(s,t)
    return best,arg
def two_row(w,D,o1,o2,o3,o4):
    W2=w+D; n=w+W2
    b=np.zeros(n,int); c=np.zeros(n,int)
    for x in range(w): b[x]=(x+1)%w
    for y in range(W2): b[w+y]=w+(y+1)%W2
    for x in range(w): c[x]=w+(x+o1)%W2
    gap=[(o1+w+k)%W2 for k in range(D)]
    rest=[y for y in range(W2) if (y-o2)%W2>=w]
    rest.sort(key=lambda y:(y-o2)%W2)
    for y in range(W2):
        if (y-o2)%W2<w: c[w+y]=((y-o2)%W2+o3)%w
    for k,y in enumerate(rest): c[w+y]=w+gap[(k+o4)%D]
    assert len(set(c))==n
    return b,c
