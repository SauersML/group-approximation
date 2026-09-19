# Exact lift search.  H = <a,b,d,e | u1'>, u1' = eDDEddAbDBeDDEddad.  A lift f(z) = BAS[z] n_z,
# n_z in <<w>>, with f(u1') conjugate to w^{+-1} in F(x,y) gives RP(H,G) (Tietze).  Here n_z is
# 1 or a single conjugate h w^{+-1} h^-1 with h reduced of length <= Lh.  Every candidate is decided exactly.
import sys, itertools
from verify_unimodular import BAS, W, inv, fred
from lift import U1P
def cyc(u):
    u=fred(u)
    while len(u)>1 and u[0]==u[-1].swapcase(): u=u[1:-1]
    return u
TARGETS={cyc(W),cyc(inv(W))}
def conj_eq(u):
    if len(u)!=len(W): return False
    for t in TARGETS:
        if u in t+t: return True
    return False
def red_words(L):
    out=['']; fr=['']
    for _ in range(L):
        fr=[w+c for w in fr for c in 'xXyY' if not (w and w[-1]==c.swapcase())]; out+=fr
    return out
def opts(Lh):
    o=[]
    for h in red_words(Lh):
        for r in (W,inv(W)): o.append((h,r,fred(h+r+inv(h))))
    return o
def evalf(F):
    return cyc(''.join(F[c] if c.islower() else inv(F[c.lower()]) for c in U1P))
def run(zs, Lh):
    O=opts(Lh); best=10**9; hits=[]; n=0
    for choice in itertools.product(O, repeat=len(zs)):
        F=dict(BAS)
        for z,(h,r,nw) in zip(zs,choice): F[z]=fred(BAS[z]+nw)
        u=evalf(F); n+=1
        best=min(best,len(u))
        if conj_eq(u): hits.append((zs,[(h,r==W) for h,r,_ in choice]))
    return n,best,hits
if __name__=='__main__':
    print('base f0(u1\') cyclic length',len(evalf(dict(BAS))))
    plan=[(1,int(sys.argv[1])),(2,int(sys.argv[2])),(3,int(sys.argv[3])),(4,int(sys.argv[4]))]
    for m,Lh in plan:
        if Lh<0: continue
        for zs in itertools.combinations('abde',m):
            n,best,hits=run(zs,Lh)
            print('modify',''.join(zs),'Lh',Lh,'tested',n,'min cyclic len',best,'hits',len(hits),hits[:3],flush=True)
