# independent brute-force Neuwirth test: orientable thickenability of one-vertex 2-complex
import itertools, sys
def occ(rels):
    L=[]
    for ri,r in enumerate(rels):
        for p,ch in enumerate(r):
            L.append((ri,p,ch.lower(),1 if ch.islower() else -1))
    return L
def thick(rels):
    L=occ(rels); n=len(L)
    idx={}; 
    for k,(ri,p,g,e) in enumerate(L): idx[(ri,p)]=k
    gens=sorted(set(o[2] for o in L))
    # half-edges: each occurrence k has half-edge at 'head' end of g and at 'tail' end.
    # corner between letter k=(ri,p) and next letter k'=(ri,p+1): link edge joining
    #   end of k: head if e=+1 else tail ; start of k': tail if e'=+1 else head.
    # half-edge (k,'out') := the endpoint where the letter k is exited, (k,'in') := where entered.
    twin={}
    for ri,r in enumerate(rels):
        m=len(r)
        for p in range(m):
            k=idx[(ri,p)]; k2=idx[(ri,(p+1)%m)]
            twin[(k,'out')]=(k2,'in'); twin[(k2,'in')]=(k,'out')
    def vert(h):
        k,s=h; ri,p,g,e=L[k]
        # exit of positive letter = head; entry of positive letter = tail
        end = ('head' if s=='out' else 'tail') if e==1 else ('tail' if s=='out' else 'head')
        return (g,end)
    V=set(vert(h) for h in twin)
    # components
    par={v:v for v in V}
    def f(v):
        while par[v]!=v: v=par[v]
        return v
    for h,t in twin.items(): par[f(vert(h))]=f(vert(t))
    c=len(set(f(v) for v in V))
    occs={g:[k for k in range(n) if L[k][2]==g] for g in gens}
    best=None
    lists=[]
    for g in gens:
        o=occs[g]; first=o[0]
        lists.append([ [first]+list(pp) for pp in itertools.permutations(o[1:])])
    for combo in itertools.product(*lists):
        rot={}
        for g,cyc in zip(gens,combo):
            m=len(cyc)
            for i in range(m):
                k=cyc[i]; knext=cyc[(i+1)%m]; kprev=cyc[(i-1)%m]
                # at the head vertex of g the sheets appear in cyclic order sigma; at the tail in reversed order
                for s in ('out','in'):
                    h=(k,s); v=vert(h)
                    # the half-edge of sheet knext at the same vertex
                    def he(kk):
                        for s2 in ('out','in'):
                            if vert((kk,s2))==v: return (kk,s2)
                    rot[h]= he(knext) if v[1]=='head' else he(kprev)
        # faces of phi = rot o twin
        seen=set(); F=0
        for h in twin:
            if h in seen: continue
            F+=1; x=h
            while x not in seen:
                seen.add(x); x=rot[twin[x]]
        E=n
        chi=len(V)-E+F
        if chi==2*c: return True, combo
    return False, None
rels=sys.argv[1:]
print(rels, thick(rels)[0])
