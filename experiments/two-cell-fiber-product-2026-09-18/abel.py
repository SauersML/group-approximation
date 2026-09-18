# Unimodularity of the cylinder row c over the abelianization ring Z[s^+-,t^+-] (x->t, y->s).
import sympy as sp
s,t,S,T=sp.symbols('s t S T')
# words over basis a(alpha) b(beta) c(gamma); capitals inverses
img={'a':t,'b':s**2,'c':s}
def val(ch): return img[ch] if ch.islower() else 1/img[ch.lower()]
def fox(word,x):
    res=0; pre=1
    for ch in word:
        if ch==x: res+=pre
        if ch==x.upper(): res-=pre*val(ch)
        pre*=val(ch)
    return sp.simplify(res)
u0="abbABccBB"; u1_loop="ccccabABBB"
# based u1: tree path 0->1 is y, which is not a basis element; u1 as based loop is the loop read from vertex 1 conjugated by y.
# In Fox terms over the basis, d(y L y^-1)/dx = g * dL/dx with g = image of y = s (y is a tree path, contributes no basis letters).
g=s
c=[sp.expand(sp.simplify(g*fox(u0,x)-g*fox(u1_loop,x))) for x in 'abc']
# note: here c_x = g d u0 - g d u1 corresponds to eps g d u0 - d u1 only up to basing; recompute with u1 based at 0:
c2=[sp.expand(sp.simplify(g*fox(u0,x)-fox(u1_loop,x)*g)) for x in 'abc']
print(c)
c=[sp.expand(g*fox(u0,x)-fox(u1_loop,x)) for x in 'abc']
print("c =",c)
# clear denominators, add S*s-1, T*t-1 for Laurent ring
cn=[sp.numer(sp.together(ci)) for ci in c]
for mod in (None,2,3,5,7):
    kw={} if mod is None else {'modulus':mod}
    G=sp.groebner(cn+[S*s-1,T*t-1],S,T,s,t,order='grevlex',**kw)
    print(mod, G.exprs[:4] if len(G.exprs)>1 else G.exprs)
