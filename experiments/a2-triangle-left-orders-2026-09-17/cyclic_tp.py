# Translation-invariant triangle presentations over PG(2,q) realised as Z/N with a Singer difference set.
# lambda(x) = x + E (E a line), T = {(x,x+d1,x+d1+d2)} for chosen difference-triples (d1,d2,d3), sum 0, d_i in E.
import itertools, sys, json
def diffsets(N,k):
    out=[]
    for D in itertools.combinations(range(N),k):
        if 0 not in D: continue
        diffs=sorted((a-b)%N for a in D for b in D if a!=b)
        if diffs==sorted(list(range(1,N))*1): out.append(D)
    return out
def search(q):
    N=q*q+q+1; k=q+1; res=[]
    D0=diffsets(N,k)
    seen=set()
    for D in D0:
        for c in range(N):
            E=tuple(sorted((d+c)%N for d in D))
            if E in seen: continue
            seen.add(E)
            # candidate rotation classes
            cands=set()
            for d1 in E:
                for d2 in E:
                    d3=(-d1-d2)%N
                    if d3 in E: cands.add(min((d1,d2,d3),(d2,d3,d1),(d3,d1,d2)))
            cands=sorted(cands)
            # exact cover of E: each d1 appears as first coordinate of exactly one rotation
            def cover(c): return [c] if c[0]==c[1]==c[2] else [c[0],c[1],c[2]]
            def rec(i,used,chosen):
                if len(used)==len(E): yield list(chosen); return
                d=min(set(E)-used)
                for cl in cands:
                    cv=cover(cl)
                    if d in cv and len(set(cv))==len(cv) and not (set(cv)&used):
                        yield from rec(i+1,used|set(cv),chosen+[cl])
            for sol in rec(0,frozenset(),[]):
                tf=(0,0,0) not in sol
                res.append((E,sol,tf))
    return N,res
q=int(sys.argv[1]); N,res=search(q)
print("q",q,"N",N,"solutions",len(res),"torsion-free",sum(r[2] for r in res))
for r in res[:40]: print(r)
json.dump([(N,list(r[0]),r[1],r[2]) for r in res],open(f"cyclic_q{q}.json","w"))
