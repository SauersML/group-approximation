exec(open('h2_opp.py').read().split('# connectivity of the full opposite geometry graph')[0])
import collections
V = list(V); Al = list(Alines)
# --- product-cycle map rank over F2 ---
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
    par={a:None}; dq=collections.deque([a]); 
    while dq:
        u=dq.popleft()
        if u==b: break
        for w in treeadj[u]:
            if w not in par: par[w]=u; dq.append(w)
    if b not in par: return None
    path=[]; u=b
    while par[u] is not None: path.append((u,par[u])); u=par[u]
    return path
fund=[]
for e in E:
    if e in tree: continue
    tp=treepath(e[0],e[1])
    if tp is None: continue  # different components: no cycle
    vec={Eidx[e]}
    for (a,b) in tp:
        ee=(a,b) if (a,b) in Eidx else (b,a)
        vec ^= {Eidx[ee]}
    fund.append(vec)
print("b1(A) =",len(fund))
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
print("target dim:",k)
def loc(cv,p): return {L:(1 if Eidx[(L,p)] in cv else 0) for L in Np[p]}
rows=[]
for ci in fund:
    li={p:loc(ci,p) for p in V}
    for cj in fund:
        lj={p:loc(cj,p) for p in V}
        r=0
        for c in classes:
            ps=[v for v in V if cls[v]==c]
            for p in ps:
                f=li[p]; f0=f[Np[p][0]]
                av=[(l,f[l]%2) for l in Np[p][1:]]
                if not any(a for _,a in av): continue
                for p2 in ps:
                    g=lj[p2]; g0=g[Np[p2][0]]
                    for l,a in av:
                        if not a: continue
                        for l2 in Np[p2][1:]:
                            if g[l2]%2: r ^= 1<<slotbase[(p,p2,l,l2)]
        rows.append(r)
piv={}; rk=0
for r in rows:
    while r:
        m=r.bit_length()-1
        if m in piv: r^=piv[m]
        else: piv[m]=r; rk+=1; break
print("rank of product-cycle map mod 2:",rk,"coker2 =",k-rk)
# --- simplicial H2(Omega;F2) ---
Vs=[(('A',x),) for x in V]+[(('A',x),) for x in Al]+[(('B',x),) for x in V]+[(('B',x),) for x in Al]
def Iof(s):
    pc=[cls[x] for (_,x) in s if x in cls]
    if len(s)==2: return frozenset(pc)
    (t,x),=s
    return frozenset([cls[x]]) if x in cls else None
def allowed(sa,sb):
    Ia,Ib=Iof(sa),Iof(sb)
    if Ia is None or Ib is None: return True
    return not(len(Ia)==1 and Ia==Ib)
EsA=[tuple(sorted([('A',L),('A',p)])) for L in Al for p in adj[L] if p in cls]
EsB=[tuple(sorted([('B',L),('B',p)])) for L in Al for p in adj[L] if p in cls]
VsA=[(('A',x),) for x in V]+[(('A',x),) for x in Al]
VsB=[(('B',x),) for x in V]+[(('B',x),) for x in Al]
S1=set(EsA)|set(EsB); S2=set(); S3=set()
for sa in VsA:
    for sb in VsB:
        if allowed(sa,sb): S1.add(tuple(sorted(sa+sb)))
for ea in EsA:
    for sb in VsB:
        if allowed(ea,sb): S2.add(tuple(sorted(ea+sb)))
for sa in VsA:
    for eb in EsB:
        if allowed(sa,eb): S2.add(tuple(sorted(sa+eb)))
for ea in EsA:
    for eb in EsB:
        if allowed(ea,eb): S3.add(tuple(sorted(ea+eb)))
S1=sorted(S1); S2=sorted(S2); S3=sorted(S3)
print("counts:",len(S1),len(S2),len(S3))
i1={s:i for i,s in enumerate(S1)}; i2={s:i for i,s in enumerate(S2)}
def faces(s): return [tuple(x for j,x in enumerate(s) if j!=i) for i in range(len(s))]
def rank_rows(rows):
    piv={}; rk=0
    for r in rows:
        while r:
            m=r.bit_length()-1
            if m in piv: r^=piv[m]
            else: piv[m]=r; rk+=1; break
    return rk
r3=rank_rows([sum((1<<i2[f]) for f in faces(s) if f in i2) and __import__('functools').reduce(lambda a,f: a^(1<<i2[f]), [f for f in faces(s)],0) for s in S3])
r2=rank_rows([__import__('functools').reduce(lambda a,f: a^(1<<i1[f]), [f for f in faces(s)],0) for s in S2])
b2=(len(S2)-r2)-r3
# predicted: coker2 + dim H~2(A*B;F2) = coker2 + 2*(c-1)*b1 with c components
print("H2(Omega;F2) =",b2,"| prediction coker2 + 2*(c-1)*b1 =",(k-rk),"+",2*1*len(fund),"=",(k-rk)+2*len(fund))
