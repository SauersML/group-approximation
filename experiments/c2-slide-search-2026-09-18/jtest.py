# Module obstruction test for the Magnus family: eliminate z0 (occurring once in u_0) by u_0,
# the letters z != z0 by rho_z = z^-1 n_z BAS[z] (n_z in <<w>>), final relator R = u_1(...).
# Gamma_R -> G iso needs [R] = -h (h in G), i.e.  kappa + h in J = c' ZG^5,
# kappa = c_{z0} (d_{z0} u0)^-1, c'_z = c_z - kappa d_z u0.  Test in F_p[Q] for finite quotients Q.
import sys, numpy as np
from verify_unimodular import U0, U1, G_, W, inv, ring, fox, rmul, fromfib
from homs import group, evalw
def add(A,B,s=1):
    o=dict(A)
    for k,v in B.items(): o[k]=o.get(k,0)+s*v
    return {k:v for k,v in o.items() if v}
def gw(k): u,m=k; return fromfib(u)+('y'*m if m>0 else 'Y'*(-m))
du0={z:ring(fox(U0,z)) for z in 'abcde'}
cz={z:ring([(s,G_+u) for s,u in fox(U0,z)]+[(-s,u) for s,u in fox(U1,z)]) for z in 'abcde'}
def row(z0):
    (k,v),=du0[z0].items()
    kap=rmul(cz[z0],ring([(v,inv(gw(k)))]))
    return kap,{z:add(cz[z],rmul(kap,du0[z]),-1) for z in 'abcde' if z!=z0}
def rank_mod(M,p):
    M=M.copy()%p; r=0; rows,cols=M.shape
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i,c]: piv=i;break
        if piv is None: continue
        M[[r,piv]]=M[[piv,r]]
        M[r]=(M[r]*pow(int(M[r,c]),-1,p))%p
        nz=np.nonzero(M[:,c])[0]
        for i in nz:
            if i!=r: M[i]=(M[i]-M[i,c]*M[r])%p
        r+=1
        if r==rows: break
    return r
def homs(Q):
    N=len(Q['P']); out=[]
    for xr in Q['reps']:
        Y=np.arange(N,dtype=np.int32); X=np.full(N,xr,dtype=np.int32)
        ok=evalw(W,Q,X,Y,None if False else X)==Q['e']
        for y in Y[ok]: out.append((xr,int(y)))
    return out
def img(elt,Q,xy):
    X,Y=xy; v=np.zeros(len(Q['P']),dtype=np.int64)
    for k,c in elt.items():
        g=int(evalw(gw(k),Q,np.array([X]),np.array([Y]),np.array([Q['e']]))[0]); v[g]+=c
    return v
def test(z0,name,p):
    Q=group(name); N=len(Q['P']); mul=Q['mul']
    kap,cp=row(z0); res=[]
    for xy in homs(Q):
        # skip homs with small image? keep all
        vecs=[]
        for z,e in cp.items():
            a=img(e,Q,xy)
            for q in range(N):
                v=np.zeros(N,dtype=np.int64)
                for g in np.nonzero(a)[0]: v[mul[g,q]]+=a[g]
                vecs.append(v)
        J=np.array(vecs)%p; rJ=rank_mod(J,p)
        kv=img(kap,Q,xy)
        good=0
        for q in range(N):
            t=kv.copy(); t[q]+=1
            if rank_mod(np.vstack([J,t[None]]),p)==rJ: good+=1;break
        res.append((xy,rJ,good))
    return res
if __name__=='__main__':
    z0,name,p=sys.argv[1],sys.argv[2],int(sys.argv[3])
    res=test(z0,name,p)
    bad=[r for r in res if not r[2]]
    print(z0,name,p,'homs',len(res),'ranks',sorted(set(r[1] for r in res)),'obstructed',len(bad),bad[:3])
