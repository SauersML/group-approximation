import itertools, collections, sys
q=4
# GF(4) arithmetic: elements 0,1,2,3 as polynomials over F2 with x^2=x+1: represent ints 0..3
ADD=[[a^b for b in range(4)] for a in range(4)]
MULT=[[0]*4 for _ in range(4)]
for a in range(4):
    for b in range(4):
        # multiply polynomials a=(a1,a0) bits
        r=0
        aa=a
        for i in range(2):
            if (b>>i)&1: r ^= aa<<i
        # reduce mod x^2+x+1 (0b111)
        for i in (3,2):
            if (r>>i)&1: r ^= (0b111)<<(i-2)
        MULT[a][b]=r&3
def mul(a,b): return MULT[a][b]
def add(*xs):
    r=0
    for x in xs: r^=x
    return r
def qform(v): return add(mul(v[0],v[4]),mul(v[1],v[5]),mul(v[2],v[6]),mul(v[3],v[3]))
def Bf(x,y): return add(mul(x[0],y[4]),mul(x[4],y[0]),mul(x[1],y[5]),mul(x[5],y[1]),mul(x[2],y[6]),mul(x[6],y[2]))
def inv(a):
    for b in range(1,4):
        if mul(a,b)==1: return b
def norm(v):
    fn=next((x for x in v if x),None)
    if fn is None: return None
    iv=inv(fn); return tuple(mul(x,iv) for x in v)
pts=[]
for v in itertools.product(range(4),repeat=7):
    if any(v) and norm(v)==v and qform(v)==0: pts.append(v)
print("quadric points:",len(pts))
assert len(pts)==(4**6-1)//3
ptset=set(pts)
def addv(x,y): return tuple(a^b for a,b in zip(x,y))
def smul(s,v): return tuple(mul(s,c) for c in v)
linesQ=set()
for i in range(len(pts)):
    x=pts[i]
    for j in range(i+1,len(pts)):
        y=pts[j]
        if Bf(x,y)==0:
            mem=[]
            ok=True
            for s in range(4):
                z=norm(addv(x,smul(s,y)))
                if qform(z)!=0: ok=False; break
                mem.append(z)
            if ok:
                mem.append(norm(y))
                linesQ.add(frozenset(mem))
linesQ=[L for L in linesQ if len(L)==5]
print("quadric lines:",len(linesQ))
def pluck(L):
    a,b=sorted(L)[:2]
    return {(i,j): add(mul(a[i],b[j]),mul(a[j],b[i])) for i in range(7) for j in range(7)}
base=[((0,1),(3,6)),((1,2),(3,4)),((2,0),(3,5)),((4,5),(2,3)),((5,6),(0,3)),((6,4),(1,3))]
hex_lines=[L for L in linesQ if all(pluck(L)[a]==pluck(L)[b] for a,b in base)]
print("hex lines:",len(hex_lines))
if len(hex_lines)!=(4**6-1)//3: print("convention failed"); sys.exit(1)
cnt=collections.Counter()
for L in hex_lines:
    for x in L: cnt[x]+=1
assert all(cnt[x]==5 for x in pts)
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
print("far points:",len(V),"opp lines:",len(Al))
l1pts=[('p',x) for x in hex_lines[0]]
dl={pp:bfs(pp) for pp in l1pts}
cls={}
for v in V:
    feet=[pp for pp in l1pts if dl[pp][v]==4]; assert len(feet)==1; cls[v]=feet[0]
print("class sizes:",sorted(collections.Counter(cls.values()).values()))
sa=collections.defaultdict(set)
for L in Al:
    for p in adj[L]:
        if p in cls: sa[L].add(p); sa[p].add(L)
seen=set(); comps=[]
for n in list(V)+list(Al):
    if n in seen: continue
    c={n}; seen.add(n); dq=collections.deque([n])
    while dq:
        u=dq.popleft()
        for w in sa[u]:
            if w not in seen: seen.add(w); c.add(w); dq.append(w)
    comps.append(len([x for x in c if x[0]=='p']))
print("FULL opposition geometry point-components:",sorted(comps))

def comps_restricted(allowed_classes):
    sa2=collections.defaultdict(set)
    for L in Al:
        for p in adj[L]:
            if p in cls and cls[p] in allowed_classes: sa2[L].add(p); sa2[p].add(L)
    seen=set(); out=[]
    nodes=[v for v in V if cls[v] in allowed_classes]+list(Al)
    for n in nodes:
        if n in seen: continue
        c={n}; seen.add(n); dq=collections.deque([n])
        while dq:
            u=dq.popleft()
            for w in sa2[u]:
                if w not in seen: seen.add(w); c.add(w); dq.append(w)
        pc=len([x for x in c if x[0]=='p'])
        if pc: out.append(pc)
    return sorted(out)
allc=sorted(set(cls.values()))
print("one-deleted (4 classes):",comps_restricted(set(allc[1:]))[:8])
print("two-deleted (3 classes):",comps_restricted(set(allc[2:]))[:8])
print("three-deleted (2 classes):",comps_restricted(set(allc[3:]))[:8])
