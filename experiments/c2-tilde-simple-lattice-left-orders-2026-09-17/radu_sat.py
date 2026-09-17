# Radu's BMW lattice Gamma_R = <a,b,c,x,y,z | a^2..z^2, axax, ayay, azbz, bxbx, bycy, cxcz> (arXiv:2509.05054 Prop 3.3)
# Normal form: (reduced vertical word in x,y,z)(reduced horizontal word in a,b,c); h v -> v' h' for all 9 squares.
# K = kernel of Gamma_R -> Z/2 x Z/2 (even horizontal and even vertical length). Positive-cone SAT on K-ball.
import sys, time, itertools
from pysat.solvers import Cadical153, Glucose4
H=['a','b','c']; V=['x','y','z']
# squares h v = v' h' read from the relators (all letters involutions):
# axax: ax=xa; ayay: ay=ya; azbz: az=zb, bz=za; bxbx: bx=xb; bycy: by=yc, cy=yb; cxcz: cx=zc, cz=xc
SQ={('a','x'):('x','a'),('a','y'):('y','a'),('a','z'):('z','b'),('b','z'):('z','a'),
    ('b','x'):('x','b'),('b','y'):('y','c'),('c','y'):('y','b'),('c','x'):('z','c'),('c','z'):('x','c')}
assert len(SQ)==9 and len(set(SQ.values()))==9
# Calibration: the reducible BMW group (C2*C2*C2) x (C2*C2*C2), all squares commute; its K1 is F2 x F2 (left-orderable).
SQ_RADU=SQ
SQ_PROD={(h,v):(v,h) for h in H for v in V}
# pi_1(S_R) = kernel of Gamma_R -> D2 = <sigma_A, sigma_X>, a,b,c -> sigma_A, x,y,z -> sigma_X (paper, Example SquareRadu): K1.
KERNELS={'K1':lambda v,h: len(v)%2==0 and len(h)%2==0,
         'K2':lambda v,h: (len(h)+v.count('y'))%2==0 and len(v)%2==0}
def red(w):
    out=[]
    for c in w:
        if out and out[-1]==c: out.pop()
        else: out.append(c)
    return out
def push(hw,v):  # hw * v  = v' * hw'
    hw=list(hw)
    for i in range(len(hw)-1,-1,-1):
        v,hw[i]=SQ[(hw[i],v)]
    return v,hw
def mul(g1,g2):
    v1,h1=g1; v2,h2=g2
    vs=list(v1); h=list(h1)
    for v in v2:
        vp,h=push(h,v); vs.append(vp); vs=red(vs)
    return (tuple(red(vs)),tuple(red(h+list(h2))))
def inv(g):
    v,h=g; r=((),())
    for c in reversed(h): r=mul(r,((),(c,)))
    for c in reversed(v): r=mul(r,((c,),()))
    return r
def run(L,kern='K1',sq='radu'):
    global SQ
    SQ=SQ_RADU if sq=='radu' else SQ_PROD
    gens=[((c,),()) for c in V]+[((),(c,)) for c in H]
    ball={((),()):0}; layer=[((),())]; els=[((),())]
    for d in range(L):
        nl=[]
        for g in layer:
            for s in gens:
                n=mul(g,s)
                if n not in ball: ball[n]=len(els); els.append(n); nl.append(n)
        layer=nl
    Kel=[i for i,(v,h) in enumerate(els) if i>0 and KERNELS[kern](v,h)]
    # K is closed under products and inverses inside the ball, and has no involutions there
    for i in Kel: assert KERNELS[kern](*inv(els[i])) and inv(els[i])!=els[i]
    cls=[]
    for i in Kel:
        j=ball[inv(els[i])]
        if i<j: cls+=[[i,j],[-i,-j]]
    for i in Kel:
        for j in Kel:
            k=ball.get(mul(els[i],els[j]))
            if k is None: continue
            cls.append([-i,-j] if k==0 else [-i,-j,k])
    res=[]
    for S in (Cadical153,Glucose4):
        with S(bootstrap_with=cls) as s: res.append(s.solve())
    assert res[0]==res[1]
    return dict(group=sq,kernel=kern,radius=L,ball=len(els),K_elements=len(Kel),clauses=len(cls),sat=res[0])
if __name__=="__main__":
    sq=sys.argv[1]; kern=sys.argv[2]
    for L in map(int,sys.argv[3:]): print(run(L,kern,sq),flush=True)
