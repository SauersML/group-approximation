# One-relator lift formulation.  u0 = dEbcBADDed has c once, so pi_1(C) = H = <a,b,d,e | u1'>,
# u1' = u1(c -> gamma), gamma = BeDDEddab.  RP(H,G) follows from a lift f: F(a,b,d,e) -> F(x,y),
# f(z) in BAS[z] <<w>>, with f(u1') conjugate to w^{+-1} (Tietze: C u {x,y} u {z^-1 f(z)} ~ P_G).
from verify_unimodular import BAS, U0, U1, G_, W, inv, fred, ring, fox, rmul, nf, tox
def add(A,B,s=1):
    o=dict(A)
    for k,v in B.items(): o[k]=o.get(k,0)+s*v
    return {k:v for k,v in o.items() if v}
GAM='BeDDEddab'
def subc(u): return fred(''.join(GAM if ch=='c' else inv(GAM) if ch=='C' else ch for ch in u))
U1P=subc(U1)
def cyc(u):
    while len(u)>1 and u[0]==u[-1].swapcase(): u=u[1:-1]
    return u
def xfox(r, v):
    # Fox derivative of an x,y word r w.r.t. letter v, as ZG element
    out=[]; pre=''
    for ch in r:
        if ch==v: out.append((1,pre))
        pre+=ch
        if ch==v.upper(): out.append((-1,pre))
    return ring(out)
if __name__=='__main__':
    print('u1\' =',U1P, len(U1P))
    R0=cyc(fred(tox(U1P))); print('R0 = f0(u1\') len',len(R0))
    # class of R0 predicted: g - (d_c u1) g_c^-1 with g_c = prefix of c in u0
    gc='dEb'
    pred=ring([(1,G_)]+[(-s,p+inv(tox(gc))) for s,p in fox(U1,'c')])
    print('predicted [R0]',pred)
    for v in 'xy':
        lhs=xfox(fred(tox(U1P)),v); rhs=rmul(pred,xfox(W,v))
        print(v,'fox check',lhs==rhs)

# Both one-relator forms: eliminate z0 in {c, a} (each occurs once in u0).  Predicted class of the
# base lift: [R0] = g - (d_{z0} u1)(d_{z0} u0)^{-1}; its H-part has augmentation -e_{z0}(u1)/e_{z0}(u0) = -2.
def elim(z0):
    i=[j for j,ch in enumerate(U0) if ch.lower()==z0]; assert len(i)==1; i=i[0]
    Pw,Qw=U0[:i],U0[i+1:]
    sol=fred(inv(Pw)+inv(Qw))              # U0[i] = P^-1 Q^-1
    gam=sol if U0[i]==z0 else inv(sol)
    return fred(''.join(gam if ch==z0 else inv(gam) if ch==z0.upper() else ch for ch in U1))
def check_all():
    for z0 in 'ca':
        u=elim(z0); R=fred(tox(u))
        (s0,p0),=fox(U0,z0)
        d0=fred(p0) if s0==1 else None
        pred=ring([(1,G_)]+[(-s*s0,p+inv(p0)) for s,p in fox(U1,z0)])
        ok=all(xfox(R,v)==rmul(pred,xfox(W,v)) for v in 'xy')
        esum={z:sum(1 if ch==z else -1 if ch==z.upper() else 0 for ch in u) for z in 'abcde' if z!=z0}
        print('eliminate',z0,'relator',u,len(u),'exp sums',esum,'class',pred,'fox check',ok)
if __name__=='__main__':
    check_all()

# The only inputs of the general obstruction (proof, Steps 1-4): the basis words carry u0 to w and
# u1 to g w g^-1 in F(x,y) (so kappa0 = 1, kappa1 = g), and e(u1) = 2 e(u0) with e(u0) primitive.
def basics():
    es=lambda u:[sum(1 if ch==z else -1 if ch==z.upper() else 0 for ch in u) for z in 'abcde']
    print('BAS(u0) == w:',fred(tox(U0))==W)
    print('BAS(u1) == g w g^-1:',fred(tox(U1))==fred(G_+W+inv(G_)))
    print('e(u0) =',es(U0),'e(u1) =',es(U1),'e(u1) == 2 e(u0):',es(U1)==[2*t for t in es(U0)])
if __name__=='__main__':
    basics()
