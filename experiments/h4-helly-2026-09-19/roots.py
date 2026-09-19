import numpy as np, itertools
phi=(1+5**.5)/2
def cox(ms):
    n=len(ms); B=np.zeros((n,n))
    for i in range(n):
        for j in range(n):
            B[i,j]=1 if i==j else -np.cos(np.pi/ms[i][j])
    return B
def roots(ms):
    n=len(ms); B=cox(ms); simple=np.eye(n)
    R=[tuple(r) for r in simple]; seen={tuple(np.round(r,6)) for r in simple}; i=0
    Rl=[r for r in simple]
    while i<len(Rl):
        r=Rl[i]; i+=1
        for s in range(n):
            c=2*(r@B[:,s]) ; nr=r.copy(); nr[s]-=c
            key=tuple(np.round(nr,6)); 
            if key not in seen and tuple(np.round(-nr,6)) not in seen:
                seen.add(key); Rl.append(nr)
    return np.array(Rl),B
def M(n,edges):
    ms=[[2]*n for _ in range(n)]
    for (i,j),m in edges.items(): ms[i][j]=ms[j][i]=m
    for i in range(n): ms[i][i]=1
    return ms
