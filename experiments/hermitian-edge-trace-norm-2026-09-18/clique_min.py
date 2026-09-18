import numpy as np, sys
from scipy.optimize import minimize
rng=np.random.default_rng(int(sys.argv[2]) if len(sys.argv)>2 else 0)
m=int(sys.argv[1]); iu=np.triu_indices(m,1); E=len(iu[0])
def build(x):
    s=x[:E]; ph=x[E:]
    c=(1+s**2)*np.exp(1j*ph)
    C=np.zeros((m,m),complex); C[iu]=c; C=C+C.conj().T
    return C,s,ph,c
def f(x):
    C,s,ph,c=build(x)
    lam,V=np.linalg.eigh(C)
    S=V@np.diag(np.sign(lam))@V.conj().T
    val=np.abs(lam).sum()
    G=2*np.conj(S.T[iu]) # d/dc of tr(S C) contributions: tr(S dC)=2Re(sum S_ji dc_ij)
    G=S.T[iu]  # S_ji
    dc_ds=2*s*np.exp(1j*ph); dc_dph=1j*c
    gs=2*np.real(G*dc_ds); gph=2*np.real(G*dc_dph)
    return val,np.concatenate([gs,gph])
best=None
for t in range(int(sys.argv[3]) if len(sys.argv)>3 else 30):
    x0=np.concatenate([rng.normal(0,0.3,E),rng.uniform(0,2*np.pi,E)])
    r=minimize(f,x0,jac=True,method='L-BFGS-B',options={'maxiter':5000})
    if best is None or r.fun<best.fun: best=r
C,s,ph,c=build(best.x)
lam=np.linalg.eigvalsh(C)
print(m,"min||C||_1=%.5f ratio=%.5f"%(best.fun,best.fun/(np.sqrt(3)*(m-1))))
print(" eig",np.round(lam,4)); print(" moduli",np.round(np.abs(c),3))
