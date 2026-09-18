import numpy as np, sys
from scipy.optimize import minimize
m=int(sys.argv[1]); k=int(sys.argv[2]) if len(sys.argv)>2 else m
rng=np.random.default_rng(int(sys.argv[3]) if len(sys.argv)>3 else 0)
def E(x):
    U=(x[:m*k]+1j*x[m*k:]).reshape(m,k)
    n=np.linalg.norm(U,axis=1); V=U/n[:,None]
    G=V@V.conj().T
    Dm=np.abs(1-G)+np.eye(m)
    H=1/Dm; np.fill_diagonal(H,0)
    return H.sum()
best=1e9
for t in range(30):
    x0=rng.normal(size=2*m*k)
    r=minimize(E,x0,method='BFGS',options={'maxiter':3000})
    best=min(best,r.fun)
print(m,k,"min E=%.5f target=%.5f ratio=%.4f"%(best,np.sqrt(3)/2*(m-1)**2,best/(np.sqrt(3)/2*(m-1)**2)))
