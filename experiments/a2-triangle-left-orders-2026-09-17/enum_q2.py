# Enumerate triangle presentations (Cartwright-Mantero-Steger-Zappa) for q=2, up to relabeling.
import itertools, json
P=range(7)
LINES=[frozenset({i%7,(i+1)%7,(i+3)%7}) for i in range(7)]
def presentations():
    out=[]
    for lam in itertools.permutations(range(7)):   # lambda(x)=LINES[lam[x]]
        inc=lambda x,y: y in LINES[lam[x]]
        pairs=[(x,y) for x in P for y in P if inc(x,y)]
        cand={}
        for (x,y) in pairs:
            cand[(x,y)]=[z for z in P if inc(y,z) and inc(z,x)]
        # exact cover of pairs by cyclic classes
        T=set(); used=set()
        res=[]
        def bt():
            free=[p for p in pairs if p not in used]
            if not free:
                res.append(frozenset(T)); return
            x,y=free[0]
            for z in cand[(x,y)]:
                cl=[(x,y,z),(y,z,x),(z,x,y)]
                ps=[(x,y),(y,z),(z,x)]
                if len(set(ps))<len(ps):
                    if not (x==y==z): continue
                    ps=[(x,x)]; cl=[(x,x,x)]
                if any(p in used for p in ps): continue
                for p in ps: used.add(p)
                for t in cl: T.add(t)
                bt()
                for p in ps: used.discard(p)
                for t in cl: T.discard(t)
        bt()
        out.extend(res)
    return out
def canon(T):
    best=None
    for s in itertools.permutations(range(7)):
        key=tuple(sorted((s[a],s[b],s[c]) for a,b,c in T))
        if best is None or key<best: best=key
    return best
allT=presentations()
print("raw",len(allT))
seen={}
for T in set(allT):
    c=canon(T)
    seen.setdefault(c,T)
reps=sorted(seen)
print("classes",len(reps))
for c in reps:
    tf=all(not(a==b==c_) for a,b,c_ in c)
    print(len(c),"torsionfree" if tf else "torsion", [t for t in c if t[0]<=t[1] and t[0]<=t[2]])
json.dump([list(map(list,c)) for c in reps],open("q2_presentations.json","w"))
