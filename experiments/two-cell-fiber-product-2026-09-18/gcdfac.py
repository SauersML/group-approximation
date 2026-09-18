# For every ratio-lam configuration built by census2/finchar on n-vertex graphs, compare the gcd of the
# cylinder row c in Q[s,t] (after clearing monomials) with the Alexander polynomial of w.
import sys, sympy as sp
import census as C, finchar as FC
s,t=C.s,C.t
def fox_w(w,v):
    m={0:t,1:s,2:1/t,3:1/s}; r=0; pre=1
    for l in w:
        if l==v: r+=pre
        if l==v+2: r-=pre*m[l]
        pre*=m[l]
    return sp.factor(sp.together(r))
stats={}
orig=C.nonunit_witness
def hook(c):
    return None
# reuse finchar.run but intercept each configuration
def intercept(edges,tr,a,b,w):
    c=C.crow(0,edges,tr,a,b,w)
    cn=[sp.Poly(sp.numer(sp.together(ci)),s,t) for ci in c]
    cn=[p for p in cn if not p.is_zero]
    g=cn[0]
    for p in cn[1:]: g=sp.gcd(g,p)
    gf=sp.factor_list(g.as_expr())[1]
    gf=[f for f,e in gf if f not in (s,t)]
    d=fox_w(w,1)
    key=('gcd-nontrivial' if gf else 'gcd-trivial')
    stats[key]=stats.get(key,0)+1
    if stats[key]<=6: print(key,'gcd factors',gf,' dw/dy =',d,flush=True)
    return (0,0,0)
FC.finchar=intercept
FC.run(int(sys.argv[1]))
print(stats)
