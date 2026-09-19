import sys, io, contextlib, collections
import bfs
from lift import order
with contextlib.redirect_stdout(io.StringIO()):
    lev = bfs.main(int(sys.argv[1]))
N = 1 << int(sys.argv[1]); stats = collections.Counter()
def orbsizes(p):
    seen=set(); s=[]
    for i in range(N):
        if i in seen: continue
        j=i; l=0
        while j not in seen: seen.add(j); j=p[j]; l+=1
        s.append(l)
    return tuple(sorted(collections.Counter(s).items()))
for perms in lev.values():
    a,b,c,d = perms
    u = [(d[(x+1)%N]-d[x])%N for x in range(N)]
    aff = (u[0], d[0]) if len(set(u))==1 else None
    bor = orbsizes(b)
    stats[(aff and (aff[0], aff[1]%2), bor, orbsizes(c), orbsizes(d))] += 1
for k,v in sorted(stats.items(), key=lambda kv:-kv[1])[:25]: print(v, k)
print("classes", len(lev), "affine data (multiplier, t mod 2) over all classes:",
      sorted(collections.Counter(k[0] for k in stats.elements()).items(), key=str))
print("max order of b, c, d:", [max(order(p[i]) for p in lev.values()) for i in (1, 2, 3)],
      "min order of d:", min(order(p[3]) for p in lev.values()))
