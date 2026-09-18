# Census via fiber-product homology: for each folded graph Gamma (n vertices, letters x,y) and each
# off-diagonal component Delta of Gamma x Gamma, solve B h = lam A h, A h != 0 over Z (lam in {2,3/2}),
# build the loop prod gamma_k^{h_k} * [gamma_1,gamma_2] in Delta, freely and cyclically reduce it.
# The result w reads closed loops at v0 and v1 with z1 = lam z0 != 0.  Then run the abelian
# unimodularity test of the cylinder row c (census.crow / census.unit).
# finchar.py variant: decide non-admissibility by an exact certificate, a character chi: G -> F_q^*
# (x->t, y->s; valid since w lies in [F,F], forced by lam != 1) with c^chi = 0 in F_q^B; and test the
# abelian shadow of the normalizer obstruction (Theorem B'): [g] must lie in the image of H in Z^2.
import sys, sympy as sp
from fractions import Fraction as Fr
from fp import graphs
import census as C
def comps(n,edges):
    tr=C.mk(edges)
    V=[(a,b) for a in range(n) for b in range(n) if a!=b]
    seen=set(); out=[]
    for r in V:
        if r in seen: continue
        par={r:None}; q=[r]; order=[r]
        while q:
            u=q.pop()
            for l in range(4):
                ra=tr.get((u[0],l)); rb=tr.get((u[1],l))
                if ra and rb:
                    v=(ra[0],rb[0])
                    if v not in par: par[v]=(u,l); q.append(v); order.append(v)
        seen|=set(par); out.append((r,par))
    return tr,out
def tpath(par,v):  # word from root to v
    w=[]
    while par[v] is not None:
        u,l=par[v]; w.append(l); v=u
    return w[::-1]
def inv(w): return [(l+2)%4 for l in reversed(w)]
def red(w):
    o=[]
    for l in w:
        if o and (o[-1]-l)%4==2: o.pop()
        else: o.append(l)
    return o

DV={0:(0,1),1:(1,0),2:(0,-1),3:(-1,0)}   # letter -> exponent of (s,t) = (y,x)
def tree_pot(edges,tr,v0):
    pot={v0:(0,0)}; tree=set(); q=[v0]
    while q:
        u=q.pop()
        for l in range(4):
            r=tr.get((u,l))
            if r and r[0] not in pot:
                d=DV[l]; pot[r[0]]=(pot[u][0]+d[0],pot[u][1]+d[1]); tree.add(r[1]); q.append(r[0])
    return pot,tree
def bprime(edges,tr,v0,v1):
    pot,tree=tree_pot(edges,tr,v0)
    vecs=[]
    for i,(p,q,m) in enumerate(edges):
        if i in tree: continue
        d=DV[m]; vecs.append((pot[p][0]+d[0]-pot[q][0],pot[p][1]+d[1]-pot[q][1]))
    g=pot[v1]
    M=sp.Matrix(vecs)
    # g in the Z-span of vecs?  Smith/Hermite via sympy: solve over Z by checking lattice index
    L=sp.Matrix(vecs+[g])
    from sympy.matrices.normalforms import smith_normal_form
    def inv(Mx):
        S=smith_normal_form(Mx,domain=sp.ZZ); r=[S[i,i] for i in range(min(S.shape)) if S[i,i]!=0]
        return len(r),abs(sp.prod(r))
    return inv(M)==inv(L)
PR=[3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61]
def finchar(edges,tr,v0,v1,w):
    pot,tree=tree_pot(edges,tr,v0)
    basis=[i for i in range(len(edges)) if i not in tree]
    for q in PR:
        for sv in range(1,q):
            for tv in range(1,q):
                val={0:tv,1:sv,2:pow(tv,q-2,q),3:pow(sv,q-2,q)}
                def pw(e): return pow(sv,e[0]%(q-1),q)*pow(tv,e[1]%(q-1),q)%q
                def fox(v):
                    d={i:0 for i in basis}; pre=pw(pot[v]); vv=v
                    for l in w:
                        v2,i,sg=tr[(vv,l)]
                        if i in d:
                            d[i]=(d[i]+pre)%q if sg==1 else (d[i]-pre*val[l])%q
                        pre=pre*val[l]%q; vv=v2
                    return d
                d0=fox(v0); d1=fox(v1); g=pw(pot[v1])
                if all((g*d0[i]-d1[i])%q==0 for i in basis): return (q,sv,tv)
    return None
def run(n,lams=(Fr(2),Fr(3,2))):
    res={}; shown=[0]
    for edges in graphs(n):
        NE=len(edges); C.NE=NE
        tr,cs=comps(n,edges)
        for r,par in cs:
            gens=[]
            for u in par:
                for l in range(4):
                    ra=tr.get((u[0],l)); rb=tr.get((u[1],l))
                    if not(ra and rb): continue
                    v=(ra[0],rb[0])
                    if par.get(v)==(u,l) or (l>=2 and par.get(u)==(v,(l+2)%4)): continue
                    if l>=2: continue
                    gens.append(red(tpath(par,u)+[l]+inv(tpath(par,v))))
            if len(gens)<2: continue
            Z=[]
            for gw in gens:
                z0=C.read(tr,r[0],gw)[1]; z1=C.read(tr,r[1],gw)[1]; Z.append((z0,z1))
            for lam in lams:
                M=sp.Matrix([[z1[i]-lam*z0[i] for i in range(NE)] for z0,z1 in Z]).T
                for h in M.nullspace():
                    h=sp.Matrix(h); den=sp.ilcm(*[sp.fraction(x)[1] for x in h]); h=[int(x*den) for x in h]
                    A=[sum(h[k]*Z[k][0][i] for k in range(len(Z))) for i in range(NE)]
                    if not any(A): continue
                    w=[]
                    for k,hk in enumerate(h):
                        w+= (gens[k] if hk>0 else inv(gens[k]))*abs(hk)
                    w+=gens[0]+gens[1]+inv(gens[0])+inv(gens[1])
                    w=red(w)
                    # cyclic reduction, tracking the base pair
                    a,b=r
                    while len(w)>1 and (w[0]-w[-1])%4==2:
                        a=C.read(tr,a,[w[0]])[0]; b=C.read(tr,b,[w[0]])[0]; w=w[1:-1]
                    if C.pp(w) or len(w)<4: continue
                    ra=C.read(tr,a,w); rb=C.read(tr,b,w)
                    assert ra[0]==a and rb[0]==b and all(y==lam*x for x,y in zip(ra[1],rb[1]))
                    bp=bprime(edges,tr,a,b)
                    wit=finchar(edges,tr,a,b,w)
                    key=('Bprime-ok' if bp else 'Bprime-FAIL','nonadm-char' if wit else 'open',str(lam)); res[key]=res.get(key,0)+1
                    if not wit: print('OPEN',edges,a,b,''.join(C.LET[l] for l in w),lam,'Bprime',bp,flush=True)
                    elif shown[0]<5: shown[0]+=1; print('certificate',edges,a,b,lam,'char (q,s,t)=',wit,'len',len(w),flush=True)
                    break
    return res
if __name__=="__main__":
    print(run(int(sys.argv[1])),flush=True)
