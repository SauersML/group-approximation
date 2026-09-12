import itertools, collections, numpy as np
q=3
# grid twisted level: A = K_{q+1, q} bipartite (points p_0..p_q, lines l_1..l_q), all edges
pts=[('p',i) for i in range(q+1)]; lns=[('l',a) for a in range(1,q+1)]
E=[(l,p) for l in lns for p in pts]
Eidx={e:i for i,e in enumerate(E)}
# classes: class of point p_i = i; single-class vertices = points; lines all-class
# cycle basis of K_{q+1,q}: b1 = (q+1)q - (2q+1) + 1
import numpy as np
b1=(q+1)*q-(2*q+1)+1
# fundamental cycles via spanning tree
parent={}
def find(x):
    while parent.get(x,x)!=x: parent[x]=parent.get(parent[x],parent[x]); x=parent[x]
    return x
tree=set(); adjT=collections.defaultdict(set)
for e in E:
    a,b=find(e[0]),find(e[1])
    if a!=b: parent[a]=b; tree.add(e); adjT[e[0]].add(e[1]); adjT[e[1]].add(e[0])
fund=[]
for e in E:
    if e in tree: continue
    par={e[0]:None}; dq=collections.deque([e[0]])
    while dq:
        u=dq.popleft()
        if u==e[1]: break
        for w in adjT[u]:
            if w not in par: par[w]=u; dq.append(w)
    vec=collections.defaultdict(int); vec[Eidx[e]]+=1
    u=e[1]
    while par[u] is not None:
        a,b2=u,par[u]
        ee=(a,b2) if (a,b2) in Eidx else (b2,a)
        vec[Eidx[ee]] += 1 if ee[0]==a else -1
        u=b2
    fund.append(dict(vec))
assert len(fund)==b1, (len(fund),b1)
Np={p:lns for p in pts}
slot={}; k=0
for i in range(q+1):
    p=('p',i)
    for l in lns[1:]:
        for l2 in lns[1:]:
            slot[(i,l,l2)]=k; k+=1
rows=np.zeros((b1*b1,k),dtype=np.int64); r=0
def locv(cv,p): return {l: cv.get(Eidx[(l,p)],0) for l in lns}
for ci in fund:
    for cj in fund:
        row=rows[r]
        for i in range(q+1):
            p=('p',i)
            f=locv(ci,p); g=locv(cj,p)
            for l in lns[1:]:
                if f[l]:
                    for l2 in lns[1:]:
                        if g[l2]: row[slot[(i,l,l2)]]=f[l]*g[l2]
        r+=1
def rank_modp(M,p):
    A=(M%p).astype(np.int64); m,n=A.shape; rank=0; rp=0
    for col in range(n):
        piv=None
        for rr in range(rp,m):
            if A[rr,col]%p: piv=rr; break
        if piv is None: continue
        A[[rp,piv]]=A[[piv,rp]]
        A[rp]=(A[rp]*pow(int(A[rp,col]),p-2,p))%p
        cv=A[:,col].copy(); cv[rp]=0
        A=(A-np.outer(cv,A[rp]))%p; rank+=1; rp+=1
    return rank
print("grid level q=3: target",k,"rank mod5 =",rank_modp(rows,5),"rank mod2 =",rank_modp(rows,2))
