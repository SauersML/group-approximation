import itertools, collections, sys
q=5
def qform(v): return (v[0]*v[4]+v[1]*v[5]+v[2]*v[6]+v[3]*v[3])%q
def Bf(x,y): return (x[0]*y[4]+x[4]*y[0]+x[1]*y[5]+x[5]*y[1]+x[2]*y[6]+x[6]*y[2]+2*x[3]*y[3])%q
def norm(v):
    fn=next((x for x in v if x),None)
    if fn is None: return None
    iv=pow(fn,q-2,q); return tuple((x*iv)%q for x in v)
pts=[]
for v in itertools.product(range(q),repeat=7):
    if any(v) and norm(v)==v and qform(v)==0: pts.append(v)
print("pts:",len(pts)); assert len(pts)==(q**6-1)//(q-1)
linesQ=set()
n=len(pts)
for i in range(n):
    x=pts[i]
    if i%500==0: pass
    for j in range(i+1,n):
        y=pts[j]
        if Bf(x,y)==0:
            ok=True; mem=[norm(y)]
            for s in range(q):
                z=norm(tuple((x[k]+s*y[k])%q for k in range(7)))
                if qform(z)!=0: ok=False; break
                mem.append(z)
            if ok: linesQ.add(frozenset(mem))
linesQ=[L for L in linesQ if len(L)==q+1]
print("quadric lines:",len(linesQ))
def pluck(L):
    a,b=sorted(L)[:2]
    return {(i,j):(a[i]*b[j]-a[j]*b[i])%q for i in range(7) for j in range(7)}
base=[((0,1),(3,6)),((1,2),(3,4)),((2,0),(3,5)),((4,5),(2,3)),((5,6),(0,3)),((6,4),(1,3))]
found=None
for signs in itertools.product([1,q-1],repeat=6):
    cs=[(a,b,s) for (a,b),s in zip(base,signs)]
    hl=[L for L in linesQ if all(pluck(L)[a]==(s*pluck(L)[b])%q for a,b,s in cs)]
    if len(hl)==(q**6-1)//(q-1):
        cnt=collections.Counter()
        for L in hl:
            for x in L: cnt[x]+=1
        if all(cnt[x]==q+1 for x in pts): found=(hl,signs); break
if not found: print("no convention"); sys.exit(1)
hex_lines,signs=found
print("signs:",signs)
adj=collections.defaultdict(set)
for li,L in enumerate(hex_lines):
    for x in L: adj[('p',x)].add(('l',li)); adj[('l',li)].add(('p',x))
def bfs(s):
    d={s:0}; dq=collections.deque([s])
    while dq:
        u=dq.popleft()
        for w in adj[u]:
            if w not in d: d[w]=d[u]+1; dq.append(w)
    return d
l1=('l',0); d=bfs(l1)
V=[x for x in adj if x[0]=='p' and d[x]==5]; Al=[x for x in adj if x[0]=='l' and d[x]==6]
print("far:",len(V),"opp:",len(Al))
l1pts=[('p',x) for x in hex_lines[0]]
dl={pp:bfs(pp) for pp in l1pts}
cls={}
for v in V:
    feet=[pp for pp in l1pts if dl[pp][v]==4]; assert len(feet)==1; cls[v]=feet[0]
allc=sorted(set(cls.values()))
print("class sizes:",sorted(collections.Counter(cls.values()).values()))
def comps_restricted(allowed):
    sa=collections.defaultdict(set)
    for L in Al:
        for p in adj[L]:
            if p in cls and cls[p] in allowed: sa[L].add(p); sa[p].add(L)
    seen=set(); out=[]
    for nd in [v for v in V if cls[v] in allowed]+list(Al):
        if nd in seen: continue
        c={nd}; seen.add(nd); dq=collections.deque([nd])
        while dq:
            u=dq.popleft()
            for w in sa[u]:
                if w not in seen: seen.add(w); c.add(w); dq.append(w)
        pc=len([x for x in c if x[0]=='p'])
        if pc or len(c)>1: out.append(pc)
    return sorted(x for x in out if x>0)
for k in range(6,1,-1):
    cc=comps_restricted(set(allc[:k]))
    print(f"k={k} classes: components:",len(cc),"sizes:",sorted(set(cc)))
