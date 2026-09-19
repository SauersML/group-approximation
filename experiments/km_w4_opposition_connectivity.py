import itertools, collections
# GF(4)
MULT=[[0]*4 for _ in range(4)]
for a in range(4):
    for b in range(4):
        r=0; 
        for i in range(2):
            if (b>>i)&1: r ^= a<<i
        for i in (3,2):
            if (r>>i)&1: r ^= 0b111<<(i-2)
        MULT[a][b]=r&3
def mul(a,b): return MULT[a][b]
def inv(a): return next(b for b in range(1,4) if mul(a,b)==1)
def norm(v):
    fn=next((x for x in v if x),None)
    iv=inv(fn); return tuple(mul(x,iv) for x in v)
pts=[]
for v in itertools.product(range(4),repeat=4):
    if any(v) and norm(v)==v: pts.append(v)
assert len(pts)==85
def B(x,y): return mul(x[0],y[1])^mul(x[1],y[0])^mul(x[2],y[3])^mul(x[3],y[2])
lines=set()
for i in range(len(pts)):
    for j in range(i+1,len(pts)):
        x,y=pts[i],pts[j]
        if B(x,y)==0:
            mem=[norm(y)]
            for s in range(4):
                mem.append(norm(tuple(x[k]^mul(s,y[k]) for k in range(4))))
            lines.add(frozenset(mem))
lines=[L for L in lines if len(L)==5]
print("W(4) lines:",len(lines))
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
V=[x for x in adj if x[0]=='p' and d[x]==3]; Al=[x for x in adj if x[0]=='l' and d[x]==4]
print("far:",len(V),"opp:",len(Al))
l1pts=[('p',x) for x in lines[0]]
dl={pp:bfs(pp) for pp in l1pts}
cls={}
for v in V:
    feet=[pp for pp in l1pts if dl[pp][v]==2]; assert len(feet)==1; cls[v]=feet[0]
allc=sorted(set(cls.values()))
print("class sizes:",sorted(collections.Counter(cls.values()).values()))
def comps(allowed):
    sa=collections.defaultdict(set)
    for L in Al:
        for p in adj[L]:
            if p in cls and cls[p] in allowed: sa[L].add(p); sa[p].add(L)
    seen=set(); out=[]
    for n in [v for v in V if cls[v] in allowed]+list(Al):
        if n in seen: continue
        c={n}; seen.add(n); dq=collections.deque([n])
        while dq:
            u=dq.popleft()
            for w in sa[u]:
                if w not in seen: seen.add(w); c.add(w); dq.append(w)
        pc=len([x for x in c if x[0]=='p'])
        if pc: out.append(pc)
    return sorted(out)
for k in range(5,1,-1):
    cc=comps(set(allc[:k]))
    print(f"k={k}: {len(cc)} components, sizes {sorted(set(cc))}")
