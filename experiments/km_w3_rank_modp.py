exec(open('w3_opp.py').read().split('# --- rational surjectivity')[0])
import collections, numpy as np
E=[(L,p) for L in Al for p in adj[L] if p in cls]
Eidx={e:i for i,e in enumerate(E)}
parent={}
def find(x):
    while parent.get(x,x)!=x: parent[x]=parent.get(parent[x],parent[x]); x=parent[x]
    return x
tree=set()
for e in E:
    a,b=find(e[0]),find(e[1])
    if a!=b: parent[a]=b; tree.add(e)
treeadj=collections.defaultdict(set)
for (L,p) in tree: treeadj[L].add(p); treeadj[p].add(L)
def treepath(a,b):
    par={a:None}; dq=collections.deque([a])
    while dq:
        u=dq.popleft()
        if u==b: break
        for w in treeadj[u]:
            if w not in par: par[w]=u; dq.append(w)
    path=[]; u=b
    while par[u] is not None: path.append((u,par[u])); u=par[u]
    return path
# integer cycle vectors with signs: orient each edge (L,p) as L->p; cycle = alternating path
fund=[]
for e in E:
    if e in tree: continue
    vec=collections.defaultdict(int)
    # cycle: e followed by tree path from e[1] back to e[0]; assign +1 to e traversed L->p
    vec[Eidx[e]] += 1
    # path edges: traverse from e[1] (a point) to e[0] (a line); each step (u,par) traversed u->par
    for (u,pu) in treepath(e[0], e[1])[::-1]:
        # we walk from e[1] up to e[0]: reversed list gives steps from e[1]? treepath returns edges from b back to a
        pass
    # simpler: walk the path from e[1] to e[0] with correct signs:
    par={e[0]:None}; dq=collections.deque([e[0]])
    while dq:
        u=dq.popleft()
        if u==e[1]: break
        for w in treeadj[u]:
            if w not in par: par[w]=u; dq.append(w)
    u=e[1]
    while par[u] is not None:
        a,b2=u,par[u]
        ee=(a,b2) if (a,b2) in Eidx else (b2,a)
        # orientation: edge stored as (L,p) meaning L->p (+1). We traverse u->par[u].
        s = 1 if (ee[0]==a) else -1  # traversing L->p gives +1, p->L gives -1
        vec[Eidx[ee]] += s
        u=b2
    fund.append(dict(vec))
print("b1 =",len(fund))
Np={v:sorted([L for L in adj[v] if L in set(Al)]) for v in V}
classes=sorted(set(cls.values()))
slotbase={}; k=0
for c in classes:
    ps=[v for v in V if cls[v]==c]
    for p in ps:
        for p2 in ps:
            for l in Np[p][1:]:
                for l2 in Np[p2][1:]:
                    slotbase[(p,p2,l,l2)]=k; k+=1
print("target dim",k)
def locv(cv,p):
    # f_p(l) = coefficient of edge (l,p), sign: edge oriented L->p contributes +1*coeff to f_p(l)? 
    # local data of a cycle at p: sum of signed coefficients of edges at p; zero-sum guaranteed
    return {L: cv.get(Eidx[(L,p)],0) for L in Np[p]}
rows=np.zeros((len(fund)**2, k), dtype=np.int64)
r=0
locs=[{p:locv(cv,p) for p in V} for cv in fund]
for i,ci in enumerate(fund):
    for j,cj in enumerate(fund):
        row=rows[r]
        for c in classes:
            ps=[v for v in V if cls[v]==c]
            for p in ps:
                f=locs[i][p]
                for p2 in ps:
                    g=locs[j][p2]
                    for l in Np[p][1:]:
                        a=f[l]
                        if a:
                            for l2 in Np[p2][1:]:
                                b2=g[l2]
                                if b2: row[slotbase[(p,p2,l,l2)]] = a*b2
        r+=1
def rank_modp(M,p):
    A=(M % p).astype(np.int64)
    m,n=A.shape; rank=0; rowptr=0
    for col in range(n):
        piv=None
        for rr in range(rowptr,m):
            if A[rr,col]%p: piv=rr; break
        if piv is None: continue
        A[[rowptr,piv]]=A[[piv,rowptr]]
        inv=pow(int(A[rowptr,col]),p-2,p)
        A[rowptr]=(A[rowptr]*inv)%p
        colvals=A[:,col].copy(); colvals[rowptr]=0
        A=(A - np.outer(colvals, A[rowptr]))%p
        rank+=1; rowptr+=1
        if rowptr==m: break
    return rank
# sanity: cycle rows should be zero-sum locally: check a few
print("rank mod 5 =", rank_modp(rows,5))
print("rank mod 7 =", rank_modp(rows,7))
