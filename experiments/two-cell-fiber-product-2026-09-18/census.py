# Census: folded graphs Gamma on {x,y}, n vertices; for off-diagonal (v0,v1) find words w (cyclically
# reduced, not a proper power, length <= L) reading closed loops at v0 and v1 with z1 = lam*z0 != 0,
# lam in {2,1/2,3/2,2/3}. For each, compute the cylinder row c over Q[s^+-,t^+-] (x->t, y->s) and
# test whether it generates the unit ideal (abelian admissibility test).
import sys, itertools, sympy as sp
from fractions import Fraction as Fr
from fp import graphs, analyse
s,t,S,T=sp.symbols('s t S T')
LET='xyXY'
def mk(edges):
    out={}
    for i,(a,b,m) in enumerate(edges):
        out[(a,m)]=(b,i,1); out[(b,m+2)]=(a,i,-1)
    return out
def read(tr,v,w):
    z=[0]*NE; path=[]
    for l in w:
        r=tr.get((v,l))
        if r is None: return None
        v2,i,sg=r; z[i]+=sg; path.append((v,l,i,sg)); v=v2
    return v,z,path
def pp(w):
    n=len(w); return any(n%d==0 and w==w[:d]*(n//d) for d in range(1,n))
def findwords(tr,v0,v1,L,maxhits=1):
    hits=[]
    st=[((),v0,v1)]
    while st and len(hits)<maxhits:
        w,a,b=st.pop()
        if len(w)>=4 and a==v0 and b==v1 and (w[0]-w[-1])%4!=2 and not pp(list(w)):
            z0=read(tr,v0,w)[1]; z1=read(tr,v1,w)[1]
            if any(z0):
                for lam in (Fr(2),Fr(1,2),Fr(3,2),Fr(2,3)):
                    if all(y==lam*x for x,y in zip(z0,z1)): hits.append((w,lam)); break
        if len(w)==L: continue
        for l in range(4):
            if w and (l-w[-1])%4==2: continue
            ra=tr.get((a,l)); rb=tr.get((b,l))
            if ra and rb: st.append((w+(l,),ra[0],rb[0]))
    return hits
def mono(l): return {0:t,1:s,2:1/t,3:1/s}[l]
def crow(n,edges,tr,v0,v1,w):
    # spanning tree from v0, potentials pot[v] = abelian label of tree path v0->v
    pot={v0:sp.Integer(1)}; tree=set(); q=[v0]
    while q:
        u=q.pop()
        for l in range(4):
            r=tr.get((u,l))
            if r and r[0] not in pot:
                pot[r[0]]=pot[u]*mono(l); tree.add(r[1]); q.append(r[0])
    basis=[i for i in range(len(edges)) if i not in tree]
    def fox(v,w):
        # Fox derivative wrt each basis edge of the loop read from v, conjugated to v0 by tree path
        d={i:sp.Integer(0) for i in basis}; pre=pot[v]
        for l in w:
            v2,i,sg=tr[(v,l)]
            if i in basis:
                if sg==1: d[i]+=pre
                else: d[i]-=pre*mono(l)
            pre=pre*mono(l); v=v2
        return d
    d0=fox(v0,w); d1=fox(v1,w); g=pot[v1]
    return [sp.expand(g*d0[i]-d1[i]) for i in basis]
def unit(c):
    cn=[sp.numer(sp.together(ci)) for ci in c]
    G=sp.groebner(cn+[S*s-1,T*t-1],S,T,s,t,order='grevlex')
    return G.exprs==[1]
if __name__=="__main__":
    n=int(sys.argv[1]); L=int(sys.argv[2])
    res={'unit':0,'nonunit':0}; shown=0
    for edges in graphs(n):
        NE=len(edges); tr=mk(edges)
        pairs=sorted(set(h[0] for h in analyse(n,edges,[Fr(2),Fr(3,2)])))
        for v0,v1 in pairs:
            if True:
                for w,lam in findwords(tr,v0,v1,L):
                    c=crow(n,edges,tr,v0,v1,w)
                    u=unit(c); res['unit' if u else 'nonunit']+=1
                    if u or shown<3:
                        shown+=1; print('UNIT' if u else 'nonunit',edges,v0,v1,''.join(LET[l] for l in w),lam,flush=True)
    print(res)

def nonunit_witness(c):
    """Certify non-unimodularity over Q[s^+-,t^+-]: find a specialization t=s^k or t=q under which
    the numerators have a common factor other than a power of s.  Returns the specialization or None."""
    cn=[sp.numer(sp.together(ci)) for ci in c]
    specs=[('t=s^%d'%k, s**k) for k in range(-3,4)]+[('t=%d'%q, sp.Integer(q)) for q in (-1,2,-2,3)]
    for name,val in specs:
        ps=[sp.Poly(sp.numer(sp.together(ci.subs(t,val))),s) for ci in cn]
        ps=[p for p in ps if not p.is_zero]
        if not ps: return name
        g=ps[0]
        for p in ps[1:]: g=sp.gcd(g,p)
        # strip powers of s
        while g.degree()>0 and g.eval(0)==0: g=sp.Poly(sp.quo(g.as_expr(),s),s)
        if g.degree()>0: return name+' gcd='+str(g.as_expr())
    return None
