# Positive-cone SAT for the type-preserving subgroup pi_1(S) of a one-vertex BMW group.
# A BMW group acts simply transitively on the vertices of T x T; each relator h1 v1 h2 v2 gives four
# corner equations h v = v' h', and together they are a bijection on (h,v) pairs.  Hence every element has a
# unique normal form (freely reduced vertical word)(freely reduced horizontal word).
# K = even horizontal length and even vertical length = kernel of Gamma -> <sigma_A, sigma_X> = Z/2 x Z/2,
# which is pi_1 of the 4-vertex square complex S (arXiv:2509.05054, Examples SquareRadu and JanzenWise).
import sys, random
from pysat.solvers import Cadical153, Glucose4
GROUPS={
 # Radu: all generators involutions
 'radu':dict(H='abc',V='xyz',inv={c:c for c in 'abcxyz'},
             rel=['axax','ayay','azbz','bxbx','bycy','cxcz']),
 # Janzen-Wise: capital letter = inverse
 'jw':dict(H='abAB',V='xyXY',inv={'a':'A','A':'a','b':'B','B':'b','x':'X','X':'x','y':'Y','Y':'y'},
           rel=['axay','aXbY','aYBX','bxBY']),
}
def prod_group(name,base):  # reducible calibration: same letters, all squares commute
    g=dict(GROUPS[base]); g['rel']=None; GROUPS[name]=g
prod_group('prod_radu','radu'); prod_group('prod_jw','jw')
def build(name):
    G=GROUPS[name]; H,V,I=G['H'],G['V'],G['inv']
    if G['rel'] is None:
        SQ={(h,v):(v,h) for h in H for v in V}
    else:
        SQ={}
        def put(h,v,v2,h2):
            assert (h,v) not in SQ or SQ[(h,v)]==(v2,h2),(h,v); SQ[(h,v)]=(v2,h2)
        for r in G['rel']:
            h1,v1,h2,v2=r
            put(h1,v1,I[v2],I[h2]); put(h2,v2,I[v1],I[h1])
            put(I[h2],I[v1],v2,h1); put(I[h1],I[v2],v1,h2)
    assert len(SQ)==len(H)*len(V) and len(set(SQ.values()))==len(SQ)
    return H,V,I,SQ
def make(name):
    H,V,I,SQ=build(name)
    def red(w):
        out=[]
        for c in w:
            if out and out[-1]==I[c]: out.pop()
            else: out.append(c)
        return out
    def push(hw,v):
        hw=list(hw)
        for i in range(len(hw)-1,-1,-1): v,hw[i]=SQ[(hw[i],v)]
        return v,hw
    def mul(g1,g2):
        vs=list(g1[0]); h=list(g1[1])
        for v in g2[0]:
            vp,h=push(h,v); vs=red(vs+[vp])
        return (tuple(vs),tuple(red(h+list(g2[1]))))
    def word(w):
        g=((),())
        for c in w: g=mul(g,((c,),()) if c in V else ((),(c,)))
        return g
    def inv(g):
        return word([I[c] for c in reversed(g[0]+g[1])])
    return H,V,I,SQ,mul,word,inv
def confluence(name):
    # String rewriting: c I[c] -> empty, h v -> v' h'.  Terminates (length does not grow and the number of
    # (horizontal before vertical) letter pairs strictly drops).  Check every critical pair
    # (overlaps h I[h] v, h v I[v], c I[c] c); by Newman's lemma the system is complete.
    H,V,I,SQ=build(name)
    def rw(w):
        w=list(w); changed=True
        while changed:
            changed=False
            for i in range(len(w)-1):
                p,q=w[i],w[i+1]
                if I[p]==q: del w[i:i+2]; changed=True; break
                if p in H and q in V: w[i],w[i+1]=SQ[(p,q)]; changed=True; break
        return tuple(w)
    n=0
    for h in H:
        for v in V:
            v2,h2=SQ[(h,v)]
            # h I[h] v : cancel -> v ; rewrite I[h] v first -> h v'' h''
            v3,h3=SQ[(I[h],v)]; assert rw([h,v3,h3])==(v,),(h,v)
            # h v I[v] : cancel -> h ; rewrite h v first -> v2 h2 I[v]
            assert rw([v2,h2,I[v]])==(h,),(h,v); n+=2
    for c in H+V: assert rw([c,I[c],c])==(c,); n+=1
    G=GROUPS[name]
    for r in (G['rel'] or []): assert rw(r)==(),r
    return n
def selftest(name,trials=2000):
    confluence(name)
    H,V,I,SQ,mul,word,inv=make(name)
    G=GROUPS[name]
    if G['rel']:
        for r in G['rel']: assert word(r)==((),()),r
    L=list(H+V); rnd=random.Random(1)
    for _ in range(trials):
        a,b,c=[word([rnd.choice(L) for _ in range(rnd.randint(0,7))]) for _ in range(3)]
        assert mul(mul(a,b),c)==mul(a,mul(b,c))
        assert mul(a,inv(a))==((),())
def run(name,L):
    selftest(name)
    H,V,I,SQ,mul,word,inv=make(name)
    gens=[((c,),()) for c in V]+[((),(c,)) for c in H]
    e=((),()); ball={e:0}; els=[e]; layer=[e]
    for d in range(L):
        nl=[]
        for g in layer:
            for s in gens:
                n=mul(g,s)
                if n not in ball: ball[n]=len(els); els.append(n); nl.append(n)
        layer=nl
    Kel=[i for i,(v,h) in enumerate(els) if i>0 and len(v)%2==0 and len(h)%2==0]
    for i in Kel: assert inv(els[i])!=els[i]   # no involutions in K inside the ball
    cls=[]
    for i in Kel:
        j=ball[inv(els[i])]
        if i<j: cls+=[[i,j],[-i,-j]]
    for i in Kel:
        gi=els[i]; li=len(gi[0])+len(gi[1])
        for j in Kel:
            gj=els[j]
            k=ball.get(mul(gi,gj))
            if k is None: continue
            cls.append([-i,-j] if k==0 else [-i,-j,k])
    res=[]
    for S in (Cadical153,Glucose4):
        with S(bootstrap_with=cls) as s: res.append(s.solve())
    assert res[0]==res[1]
    return dict(group=name,radius=L,ball=len(els),K_elements=len(Kel),clauses=len(cls),sat=res[0])
if __name__=="__main__":
    name=sys.argv[1]
    print(name,'critical pairs resolved:',confluence(name))
    for L in map(int,sys.argv[2:]): print(run(name,L),flush=True)
