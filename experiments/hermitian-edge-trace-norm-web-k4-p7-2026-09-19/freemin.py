# min ||C||_1 on P_7^4 when edges in F are free (any complex value)
import numpy as np, sys, itertools
from scipy.optimize import minimize
w,k=7,4
E=[(i,j) for i in range(w) for j in range(i+1,w) if j-i<=k]
def run(F,rest=12,seed=0):
    rng=np.random.default_rng(seed); m=len(E); best=1e9
    I=np.array([e[0] for e in E]); J=np.array([e[1] for e in E]); fr=np.array([e in F for e in E])
    def f(x):
        t=np.where(fr,x[:m],1+x[:m]**2); th=x[m:]
        C=np.zeros((w,w),complex); v=t*np.exp(1j*th); C[I,J]=v; C[J,I]=np.conj(v)
        return np.abs(np.linalg.eigvalsh(C)).sum()
    for r in range(rest):
        x0=np.concatenate([rng.normal(0,.3,m),rng.uniform(0,2*np.pi,m)])
        res=minimize(f,x0,method='BFGS',options={'maxiter':3000,'gtol':1e-9})
        res=minimize(f,res.x,method='Nelder-Mead',options={'maxiter':20000,'xatol':1e-10,'fatol':1e-12})
        best=min(best,res.fun)
    return best
if __name__=="__main__":
    size=int(sys.argv[1])
    # up to reflection i->6-i
    seen=set()
    for F in itertools.combinations(E,size):
        key=tuple(sorted(F)); ref=tuple(sorted((6-j,6-i) for (i,j) in F))
        if ref in seen: continue
        seen.add(key)
        print(size,F,"%.4f"%run(set(F)),flush=True)
