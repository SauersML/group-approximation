# Enumerate one-vertex complete VH square complexes (BMW data) of degree (m,n).
# Horizontal letters 0..m-1 with involution iA (p pairs (0,1),(2,3),..., rest fixed); vertical likewise.
# Datum: SQ, a bijection A x B -> B x A, (h,v) -> (v',h') meaning h v = v' h', closed under the Klein orbit
#   (h,v)->(v',h');  (iA h', iB v')->(iB v, iA h);  (h', iB v)->(iB v', h);  (iA h, v')->(v, iA h').
import itertools, sys, json
def inv_arr(m,p):
    a=list(range(m))
    for k in range(p): a[2*k],a[2*k+1]=2*k+1,2*k
    return a
def orbit(iA,iB,h,v,v2,h2):
    return [((h,v),(v2,h2)),((iA[h2],iB[v2]),(iB[v],iA[h])),((h2,iB[v]),(iB[v2],h)),((iA[h],v2),(v,iA[h2]))]
def enumerate_data(m,pA,n,pB):
    iA=inv_arr(m,pA); iB=inv_arr(n,pB)
    corners=[(h,v) for h in range(m) for v in range(n)]
    targets=[(v,h) for v in range(n) for h in range(m)]
    SQ={}; img=set(); out=[]
    def rec():
        c=None
        for x in corners:
            if x not in SQ: c=x; break
        if c is None:
            out.append(dict(SQ)); return
        h,v=c
        for (v2,h2) in targets:
            if (v2,h2) in img: continue
            orb=orbit(iA,iB,h,v,v2,h2)
            new={}; ok=True
            for a,b in orb:
                if a in SQ:
                    if SQ[a]!=b: ok=False; break
                elif a in new:
                    if new[a]!=b: ok=False; break
                else: new[a]=b
            if not ok: continue
            vals=list(new.values())
            if len(set(vals))!=len(vals) or any(b in img for b in vals): continue
            for a,b in new.items(): SQ[a]=b; img.add(b)
            rec()
            for a,b in new.items(): del SQ[a]; img.discard(b)
    rec()
    return iA,iB,out
def syms(m,iA):
    return [p for p in itertools.permutations(range(m)) if all(p[iA[x]]==iA[p[x]] for x in range(m))]
def key(SQ): return tuple(sorted(SQ.items()))
def transforms(m,n,iA,iB,swap_ok):
    SA=syms(m,iA); SB=syms(n,iB)
    def relab(SQ,pA,pB): return {(pA[h],pB[v]):(pB[v2],pA[h2]) for (h,v),(v2,h2) in SQ.items()}
    def rev(SQ): return {(h,iB[v2]):(iB[v],h2) for (h,v),(v2,h2) in SQ.items()}
    def swp(SQ): return {(v,iA[h2]):(iA[h],v2) for (h,v),(v2,h2) in SQ.items()}  # uses iA==iB
    return SA,SB,relab,rev,swp
def valid(SQ,m,n,iA,iB):
    if len(SQ)!=m*n or len(set(SQ.values()))!=m*n: return False
    for (h,v),(v2,h2) in SQ.items():
        for a,b in orbit(iA,iB,h,v,v2,h2):
            if SQ.get(a)!=b: return False
    return True
def census(m,pA,n,pB):
    iA,iB,data=enumerate_data(m,pA,n,pB)
    swap_ok=(m==n and pA==pB)
    SA,SB,relab,rev,swp=transforms(m,n,iA,iB,swap_ok)
    seen=set(); reps=[]
    for SQ in data:
        k=key(SQ)
        if k in seen: continue
        orbitset=set()
        base=[SQ,rev(SQ)]
        if swap_ok: base+= [swp(SQ),rev(swp(SQ))]
        for B in base:
            assert valid(B,m,n,iA,iB)
            for pA in SA:
                for pB in SB:
                    orbitset.add(key(relab(B,pA,pB)))
        seen|=orbitset
        reps.append((min(orbitset),len(orbitset)))
    return iA,iB,len(data),reps
if __name__=="__main__":
    m,pA,n,pB=map(int,sys.argv[1:5])
    iA,iB,raw,reps=census(m,pA,n,pB)
    assert sum(s for _,s in reps)==raw
    print(json.dumps(dict(m=m,pA=pA,n=n,pB=pB,raw=raw,classes=len(reps))))
    with open(f"census_{m}{pA}_{n}{pB}.json","w") as f:
        json.dump(dict(m=m,pA=pA,n=n,pB=pB,iA=iA,iB=iB,raw=raw,reps=[[list(map(list,[a[0],a[1]])) for a in r] for r,_ in reps]),f)
