import itertools, sys
q = 2
F = range(q)
# Points of PG(6,2) on the quadric x0x4+x1x5+x2x6+x3^2 = 0 (char 2)
pts = []
for v in itertools.product(F, repeat=7):
    if any(v):
        # normalize: first nonzero = 1 (char 2: automatic)
        if (v[0]*v[4] + v[1]*v[5] + v[2]*v[6] + v[3]*v[3]) % 2 == 0:
            pts.append(v)
pts = sorted(set(pts))
assert len(pts) == 63, len(pts)
B = lambda x,y: (x[0]*y[4]+x[4]*y[0]+x[1]*y[5]+x[5]*y[1]+x[2]*y[6]+x[6]*y[2]) % 2  # polar form (char2: 2*x3y3=0)
# all singular lines of Q: pairs x perp y, and check line on quadric (char 2: x+y singular too)
def addv(x,y): return tuple((a+b)%2 for a,b in zip(x,y))
linesQ = set()
for i in range(len(pts)):
    for j in range(i+1, len(pts)):
        x, y = pts[i], pts[j]
        if B(x,y)==0:
            z = addv(x,y)
            if (z[0]*z[4]+z[1]*z[5]+z[2]*z[6]+z[3]*z[3])%2==0:
                linesQ.add(frozenset([x,y,z]))
linesQ = list(linesQ)
def pluck(L):
    a, b = sorted(L)[:2]
    p = {}
    for i in range(7):
        for j in range(7):
            p[(i,j)] = (a[i]*b[j] - a[j]*b[i]) % 2
    return p
# candidate condition sets: Z3-symmetric family; search over assignments
# classical: p01=p36, p12=p34, p20=p35, p45=p23, p56=p03, p64=p13 (one convention)
cand_sets = []
base = [((0,1),(3,6)), ((1,2),(3,4)), ((2,0),(3,5)), ((4,5),(2,3)), ((5,6),(0,3)), ((6,4),(1,3))]
cand_sets.append(base)
# a few variants: swap the roles
cand_sets.append([((0,1),(3,5)), ((1,2),(3,6)), ((2,0),(3,4)), ((4,5),(1,3)), ((5,6),(2,3)), ((6,4),(0,3))])
cand_sets.append([((0,1),(6,3)), ((1,2),(4,3)), ((2,0),(5,3)), ((4,5),(3,2)), ((5,6),(3,0)), ((6,4),(3,1))])
found = None
for cs in cand_sets:
    hex_lines = []
    for L in linesQ:
        p = pluck(L)
        if all(p[a]==p[b] for a,b in cs):
            hex_lines.append(L)
    if len(hex_lines) != 63: continue
    # check: every point on exactly 3 hexagon lines
    from collections import defaultdict
    cnt = defaultdict(int)
    for L in hex_lines:
        for x in L: cnt[x]+=1
    if any(cnt[x]!=3 for x in pts): continue
    # girth of incidence graph must be 12
    import collections
    adj = defaultdict(set)
    for li,L in enumerate(hex_lines):
        for x in L:
            adj[('p',x)].add(('l',li)); adj[('l',li)].add(('p',x))
    def girth_at_least_12():
        for s in list(adj)[:40]:
            dist = {s:0}; par={s:None}; dq=collections.deque([s])
            while dq:
                u=dq.popleft()
                for w in adj[u]:
                    if w not in dist:
                        dist[w]=dist[u]+1; par[w]=u; dq.append(w)
                    elif par[u]!=w and dist[w]>=dist[u]:
                        if dist[u]+dist[w]+1 < 12: return False
        return True
    if girth_at_least_12():
        found = hex_lines; print("convention works:", cs); break
if not found: print("NO CONVENTION WORKED"); sys.exit(1)
hex_lines = found
# fix a hexagon line l1; compute the opposite-line geometry
import collections
adj = collections.defaultdict(set)
for li,L in enumerate(hex_lines):
    for x in L:
        adj[('p',x)].add(('l',li)); adj[('l',li)].add(('p',x))
def bfs_dist(src):
    dist={src:0}; dq=collections.deque([src])
    while dq:
        u=dq.popleft()
        for w in adj[u]:
            if w not in dist: dist[w]=dist[u]+1; dq.append(w)
    return dist
l1 = ('l',0)
d = bfs_dist(l1)
V = [x for x in adj if x[0]=='p' and d[x]==5]
Alines = [x for x in adj if x[0]=='l' and d[x]==6]
print("far points:", len(V), "opposite lines:", len(Alines))
# feet/classes: for each far point, its unique closest point of l1
l1pts = [('p',x) for x in hex_lines[0]]
dl = {pp: bfs_dist(pp) for pp in l1pts}
cls = {}
for v in V:
    feet = [pp for pp in l1pts if dl[pp][v]==4]
    assert len(feet)==1, (v,feet)
    cls[v]=feet[0]
from collections import Counter
print("class sizes:", Counter(cls.values()))
# each opposite line meets each class once?
for L in Alines:
    cc = [cls[p] for p in adj[L]]
    assert len(set(cc))==3, cc
# connectivity of the full opposite geometry graph (V + Alines)
sub = {x: set(w for w in adj[x] if (w in cls) or (x in cls and w in set(Alines))) for x in list(V)+list(Alines)}
subadj = collections.defaultdict(set)
for L in Alines:
    for p in adj[L]:
        if p in cls: subadj[L].add(p); subadj[p].add(L)
def components(nodes, sa):
    seen=set(); comps=[]
    for n in nodes:
        if n in seen: continue
        c=set([n]); dq=collections.deque([n]); seen.add(n)
        while dq:
            u=dq.popleft()
            for w in sa[u]:
                if w not in seen: seen.add(w); c.add(w); dq.append(w)
        comps.append(c)
    return comps
comps = components(list(V)+list(Alines), subadj)
print("FULL opposite-line geometry components:", [len([x for x in c if x[0]=='p']) for c in comps])
# one-class-deleted graphs
for delcls in set(cls.values()):
    nodes = [v for v in V if cls[v]!=delcls]+list(Alines)
    sa = collections.defaultdict(set)
    for L in Alines:
        for p in adj[L]:
            if p in cls and cls[p]!=delcls: sa[L].add(p); sa[p].add(L)
    comps2 = components(nodes, sa)
    print("deleted", delcls, "-> point-components:", sorted(len([x for x in c if x[0]=='p']) for c in comps2 if any(x[0]=='p' for x in c)))
