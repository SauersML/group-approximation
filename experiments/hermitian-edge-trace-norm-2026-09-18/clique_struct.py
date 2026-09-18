import numpy as np, sys
sys.argv=[sys.argv[0]]+sys.argv[1:]
exec(open('clique_min.py').read().split("best=None")[0])
from scipy.optimize import minimize
best=None
for t in range(int(sys.argv[3])):
    x0=np.concatenate([rng.normal(0,0.3,E),rng.uniform(0,2*np.pi,E)])
    r=minimize(f,x0,jac=True,method='L-BFGS-B',options={'maxiter':5000})
    if best is None or r.fun<best.fun: best=r
C,s,ph,c=build(best.x)
lam,V=np.linalg.eigh(C)
if abs(lam[0])<abs(lam[-1]): C=-C; lam,V=np.linalg.eigh(C)
Q=(V*np.abs(lam))@V.conj().T
print("m",m,"||C||_1",np.abs(lam).sum()); print("eig",np.round(lam,4))
print("d=q/2",np.round(np.real(np.diag(Q))/2,4))
# negative part rank1 vector
b=V[:,0]*np.sqrt(-lam[0]); ph0=b/np.abs(b); Cg=np.diag(ph0.conj())@C@np.diag(ph0)
print("gauged C (b real):"); print(np.round(Cg,3))
