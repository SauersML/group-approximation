# numerical min of ||C||_1 over admissible C on a graph (random restarts, Nelder-Mead/BFGS on smoothed params)
import numpy as np, sys
from scipy.optimize import minimize
def circ(n,D): return [(i,j) for i in range(n) for j in range(i+1,n) if min((i-j)%n,(j-i)%n) in D]
def run(n,E,rest=60,seed=0):
    rng=np.random.default_rng(seed); m=len(E); best=1e9
    def f(x):
        t=1+x[:m]**2; th=x[m:]
        C=np.zeros((n,n),complex)
        for k,(i,j) in enumerate(E): C[i,j]=t[k]*np.exp(1j*th[k]); C[j,i]=np.conj(C[i,j])
        return np.abs(np.linalg.eigvalsh(C)).sum()
    for r in range(rest):
        x0=np.concatenate([rng.normal(0,.3,m),rng.uniform(0,2*np.pi,m)])
        res=minimize(f,x0,method='BFGS',options={'maxiter':3000,'gtol':1e-9})
        res=minimize(f,res.x,method='Nelder-Mead',options={'maxiter':20000,'xatol':1e-10,'fatol':1e-12})
        best=min(best,res.fun)
    return best
if __name__=="__main__":
    n=int(sys.argv[1]); D=[int(v) for v in sys.argv[2].split(',')]; drop=[int(v) for v in sys.argv[3].split(',')] if len(sys.argv)>3 and sys.argv[3] else []
    E=circ(n,D); keep=[v for v in range(n) if v not in drop]; idx={v:k for k,v in enumerate(keep)}
    E=[(idx[i],idx[j]) for (i,j) in E if i in idx and j in idx]
    print(n,D,"drop",drop,"edges",len(E),"min",run(len(keep),E,rest=int(sys.argv[4]) if len(sys.argv)>4 else 40),flush=True)
