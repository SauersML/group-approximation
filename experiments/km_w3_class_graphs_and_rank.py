import itertools, collections, sys
q = 3
# W(3): symplectic GQ in PG(3,3): points = all of PG(3,3), lines = totally isotropic
def norm(v):
    fn=next((x for x in v if x),None)
    if fn is None: return None
    inv=pow(fn,q-2,q); return tuple((x*inv)%q for x in v)
pts=[]
for v in itertools.product(range(q),repeat=4):
    if any(v) and norm(v)==v: pts.append(v)
assert len(pts)==40
def B(x,y): return (x[0]*y[1]-x[1]*y[0]+x[2]*y[3]-x[3]*y[2])%q
lines=set()
for i in range(len(pts)):
    for j in range(i+1,len(pts)):
        x,y=pts[i],pts[j]
        if B(x,y)==0:
            mem=[norm(tuple((x[k]+a*y[k])%q for k in range(4))) for a in range(q)]+[norm(y)]
            lines.add(frozenset(mem))
lines=[L for L in lines if len(L)==q+1]
assert len(lines)==40, len(lines)
adj=collections.defaultdict(set)
for li,L in enumerate(lines):
    for x in L: adj[('p',x)].add(('l',li)); adj[('l',li)].add(('p',x))
def bfs(s):
    d={s:0}; dq=collections.deque([s])
    while dq:
        u=dq.popleft()
        for w in adj[u]:
            if w not in d: d[w]=d[u]+1; dq.append(w)
    return d
l1=('l',0); d=bfs(l1)
V=[x for x in adj if x[0]=='p' and d[x]==3]
Al=[x for x in adj if x[0]=='l' and d[x]==4]
print("far points:",len(V),"opp lines:",len(Al))
l1pts=[('p',x) for x in lines[0]]
dl={pp:bfs(pp) for pp in l1pts}
cls={}
for v in V:
    feet=[pp for pp in l1pts if dl[pp][v]==2]
    assert len(feet)==1,(v,feet); cls[v]=feet[0]
csizes=collections.Counter(cls.values())
print("class sizes:",sorted(csizes.values()))
for L in Al: assert len(set(cls[p] for p in adj[L]))==q+1
# graphs: full and class-restricted
def comps(nodes, ok):
    sa=collections.defaultdict(set)
    for L in Al:
        for p in adj[L]:
            if p in cls and ok(p): sa[L].add(p); sa[p].add(L)
    seen=set(); out=[]
    for n in nodes:
        if n in seen: continue
        c={n}; seen.add(n); dq=collections.deque([n])
        while dq:
            u=dq.popleft()
            for w in sa[u]:
                if w not in seen: seen.add(w); c.add(w); dq.append(w)
        out.append(len([x for x in c if x[0]=='p']))
    return sorted(x for x in out if x>0)
classes=list(csizes)
print("FULL:",comps(V+Al,lambda p:True))
print("two-class:",comps([v for v in V if cls[v] in classes[:2]]+Al, lambda p: cls[p] in classes[:2]))
print("three-class:",comps([v for v in V if cls[v] in classes[:3]]+Al, lambda p: cls[p] in classes[:3]))
print("one-deleted:",comps([v for v in V if cls[v]!=classes[0]]+Al, lambda p: cls[p]!=classes[0]))
# --- rational surjectivity test via rank mod 2 ---
# build cycle space basis of A (graph on V+Al with flag edges)
edges=[]
for li,L in enumerate(Al):
    for p in adj[L]:
        if p in cls: edges.append((('l',L[1]) if False else L,p))
E=[(L,p) for L in Al for p in adj[L] if p in cls]
Eidx={e:i for i,e in enumerate(E)}
# spanning forest
parent={}; 
def find(x):
    while parent.get(x,x)!=x: parent[x]=parent.get(parent[x],parent[x]); x=parent[x]
    return x
tree=set(); nodesA=set(V)|set(Al)
for e in E:
    a,b=find(e[0]),find(e[1])
    if a!=b: parent[a]=b; tree.add(e)
# fundamental cycles: for each non-tree edge, path in tree
treeadj=collections.defaultdict(set)
for (L,p) in tree: treeadj[L].add(p); treeadj[p].add(L)
def treepath(a,b):
    # bfs in tree
    par={a:None}; dq=collections.deque([a])
    while dq:
        u=dq.popleft()
        if u==b: break
        for w in treeadj[u]:
            if w not in par: par[w]=u; dq.append(w)
    path=[]; u=b
    while par[u] is not None:
        path.append((u,par[u])); u=par[u]
    return path
def cyc_vector(e):
    # edge-support of fundamental cycle of non-tree edge e, over F2 (support only)
    vec=set([Eidx[e]])
    for (a,b) in treepath(e[0],e[1]):
        ee=(a,b) if (a,b) in Eidx else (b,a)
        vec ^= {Eidx[ee]}
    return vec
fund=[cyc_vector(e) for e in E if e not in tree]
print("b1(A) =",len(fund))
# local data: for cycle-support-vector (F2), f_p = restriction at point p (F2 coefficients: cycle coefficients are +-1; mod 2 fine)
# slot coordinates: for each same-class pair (p,p'), matrix entries (l,l') with l in N(p)\{l0p}, l' in N(p')\{l0p'}
Np={}
for v in V: Np[v]=sorted([L for L in adj[v] if L in set(Al)])
slots=[]
for c in classes:
    ps=[v for v in V if cls[v]==c]
    for p in ps:
        for p2 in ps:
            slots.append((p,p2))
slotbase={}
k=0
for (p,p2) in slots:
    for l in Np[p][1:]:
        for l2 in Np[p2][1:]:
            slotbase[(p,p2,l,l2)]=k; k+=1
print("target dim:",k)
# image vectors mod 2: for cycles c (A) and c' (B=A, same geometry, identity matching of classes)
# f_p(c) in F2^{N(p)}: entries = cycle support at (l,p); reduce to Z0 coords: subtract the first line's value: coord(l) = f(l)-f(l0) -> mod 2: f(l)+f(l0)
def loc(cv, p):
    return {L:(1 if Eidx[(L,p)] in cv else 0) for L in Np[p]}
rows=[]
import random
random.seed(0)
FA=fund
# to keep it light, cap the number of product rows but ensure spanning attempt: use all pairs of a subset
sub=FA  # all
for ci in sub:
    locs_i={p: loc(ci,p) for p in V}
    for cj in sub:
        row=0
        locs_j={p: loc(cj,p) for p in V}
        bits=[]
        for (p,p2) in slots:
            f=locs_i[p]; g=locs_j[p2]
            pass_f0=0
            for l in Np[p][1:]:
                a=f[l]%2
                if a==0: continue
                for l2 in Np[p2][1:]:
                    b=g[l2]%2
                    if b==0: continue
                    bits.append(slotbase[(p,p2,l,l2)])
        r=0
        for b in bits: r |= (1<<b)
        rows.append(r)
# rank mod 2
rank=0
pivots={}
for r in rows:
    while r:
        msb=r.bit_length()-1
        if msb in pivots: r ^= pivots[msb]
        else: pivots[msb]=r; rank+=1; break
print("rank mod 2 =",rank,"of target",k)
