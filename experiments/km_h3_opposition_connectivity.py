import itertools, sys, collections
q = 3
F = range(q)
def qform(v): return (v[0]*v[4]+v[1]*v[5]+v[2]*v[6]+v[3]*v[3]) % q
pts = []
seen = set()
for v in itertools.product(F, repeat=7):
    if not any(v): continue
    # projective normalization: first nonzero = 1
    fn = next(x for x in v if x)
    if fn != 1: continue
    if qform(v)==0: pts.append(v)
assert len(pts) == (q**6-1)//(q-1), len(pts)
def Bf(x,y): return (x[0]*y[4]+x[4]*y[0]+x[1]*y[5]+x[5]*y[1]+x[2]*y[6]+x[6]*y[2]+2*x[3]*y[3]) % q
def norm(v):
    fn = next((x for x in v if x), None)
    if fn is None: return None
    inv = pow(fn, q-2, q)
    return tuple((x*inv)%q for x in v)
linesQ = set()
P = pts
for i in range(len(P)):
    for j in range(i+1, len(P)):
        x,y = P[i],P[j]
        if Bf(x,y)==0:
            ok = True
            mem = []
            for a in range(q):
                z = norm(tuple((x[k]+a*y[k])%q for k in range(7)))
                if qform(z)!=0: ok=False; break
                mem.append(z)
            zy = norm(y)
            if ok:
                linesQ.add(frozenset(mem+[zy]))
linesQ = [L for L in linesQ if len(L)==q+1]
def pluck(L):
    a,b = sorted(L)[:2]
    return {(i,j): (a[i]*b[j]-a[j]*b[i])%q for i in range(7) for j in range(7)}
base = [((0,1),(3,6)), ((1,2),(3,4)), ((2,0),(3,5)), ((4,5),(2,3)), ((5,6),(0,3)), ((6,4),(1,3))]
found=None
for signs in itertools.product([1,q-1],repeat=6):
    cs = [(a,b,s) for (a,b),s in zip(base,signs)]
    hex_lines=[L for L in linesQ if all(pluck(L)[a]==(s*pluck(L)[b])%q for a,b,s in cs)]
    if len(hex_lines)!=(q**6-1)//(q-1): continue
    cnt=collections.Counter()
    for L in hex_lines:
        for x in L: cnt[x]+=1
    if any(cnt[x]!=q+1 for x in pts): continue
    found=(hex_lines,signs); break
if not found: print("NO SIGN CONVENTION"); sys.exit(1)
hex_lines, signs = found
print("signs:", signs, "lines:", len(hex_lines))
adj = collections.defaultdict(set)
for li,L in enumerate(hex_lines):
    for x in L: adj[('p',x)].add(('l',li)); adj[('l',li)].add(('p',x))
# girth check (partial)
def girth_ok():
    cnt=0
    for s in list(adj):
        if cnt>30: break
        cnt+=1
        dist={s:0}; par={s:None}; dq=collections.deque([s])
        while dq:
            u=dq.popleft()
            for w in adj[u]:
                if w not in dist: dist[w]=dist[u]+1; par[w]=u; dq.append(w)
                elif par[u]!=w and dist[w]>=dist[u]:
                    if dist[u]+dist[w]+1<12: return False
    return True
print("girth>=12:", girth_ok())
def bfs(src):
    dist={src:0}; dq=collections.deque([src])
    while dq:
        u=dq.popleft()
        for w in adj[u]:
            if w not in dist: dist[w]=dist[u]+1; dq.append(w)
    return dist
l1=('l',0); d=bfs(l1)
V=[x for x in adj if x[0]=='p' and d[x]==5]; Al=[x for x in adj if x[0]=='l' and d[x]==6]
print("far points:", len(V), "opp lines:", len(Al))
l1pts=[('p',x) for x in hex_lines[0]]
dl={pp:bfs(pp) for pp in l1pts}
cls={}
for v in V:
    feet=[pp for pp in l1pts if dl[pp][v]==4]; assert len(feet)==1; cls[v]=feet[0]
print("class sizes:", sorted(collections.Counter(cls.values()).values()))
for L in Al:
    assert len(set(cls[p] for p in adj[L]))==q+1
sa=collections.defaultdict(set)
for L in Al:
    for p in adj[L]:
        if p in cls: sa[L].add(p); sa[p].add(L)
def comps(nodes,sa):
    seen=set(); out=[]
    for n in nodes:
        if n in seen: continue
        c={n}; seen.add(n); dq=collections.deque([n])
        while dq:
            u=dq.popleft()
            for w in sa[u]:
                if w not in seen: seen.add(w); c.add(w); dq.append(w)
        out.append(c)
    return out
cc=comps(list(V)+list(Al),sa)
print("FULL opp geometry point-components:", sorted(len([x for x in c if x[0]=='p']) for c in cc))
for delc in set(cls.values()):
    sa2=collections.defaultdict(set)
    for L in Al:
        for p in adj[L]:
            if p in cls and cls[p]!=delc: sa2[L].add(p); sa2[p].add(L)
    cc2=comps([v for v in V if cls[v]!=delc]+list(Al),sa2)
    print("deleted one class -> point-components:", sorted(len([x for x in c if x[0]=='p']) for c in cc2 if any(x[0]=='p' for x in c))[:6])
    break

# addendum: bridging statistics for one deleted class
delc = sorted(set(cls.values()))[0]
sa2=collections.defaultdict(set)
for L in Al:
    for p in adj[L]:
        if p in cls and cls[p]!=delc: sa2[L].add(p); sa2[p].add(L)
# components of the deleted graph, as sets containing lines
seen=set(); pieces=[]
for n in [v for v in V if cls[v]!=delc]+list(Al):
    if n in seen: continue
    c={n}; seen.add(n); dq=collections.deque([n])
    while dq:
        u=dq.popleft()
        for w in sa2[u]:
            if w not in seen: seen.add(w); c.add(w); dq.append(w)
    pieces.append(c)
pieces=[c for c in pieces if any(x[0]=='l' for x in c)]
print("pieces: points/lines:", [(len([x for x in c if x[0]=='p']), len([x for x in c if x[0]=='l'])) for c in pieces])
lpiece={}
for i,c in enumerate(pieces):
    for x in c:
        if x[0]=='l': lpiece[x]=i
from collections import Counter
prof=Counter()
for p in V:
    if cls[p]==delc:
        ps=tuple(sorted(Counter(lpiece[L] for L in adj[p] if L in lpiece).values()))
        prof[ps]+=1
print("bridging profiles of deleted-class points (piece multiplicities):", dict(prof))

# addendum 2: joint structure of the gradings for two deleted classes
def piece_map(delc):
    sa2=collections.defaultdict(set)
    for L in Al:
        for p in adj[L]:
            if p in cls and cls[p]!=delc: sa2[L].add(p); sa2[p].add(L)
    seen=set(); pm={}; idx=0
    for n in list(Al):
        if n in seen: continue
        c={n}; seen.add(n); dq=collections.deque([n])
        while dq:
            u=dq.popleft()
            for w in sa2[u]:
                if w not in seen: seen.add(w); c.add(w); dq.append(w)
        for x in c:
            if x[0]=='l': pm[x]=idx
        idx+=1
    return pm
cl_list = sorted(set(cls.values()))
pm0 = piece_map(cl_list[0]); pm1 = piece_map(cl_list[1]); pm2 = piece_map(cl_list[2]); pm3 = piece_map(cl_list[3])
joint = Counter((pm0[L],pm1[L]) for L in Al)
print("joint block sizes (classes 0,1):", sorted(joint.values()))
joint3 = Counter((pm0[L],pm1[L],pm2[L]) for L in Al)
print("triple blocks:", len(joint3), "sizes:", sorted(set(joint3.values())))
joint4 = Counter((pm0[L],pm1[L],pm2[L],pm3[L]) for L in Al)
print("quadruple blocks:", len(joint4), "sizes:", sorted(set(joint4.values())))
