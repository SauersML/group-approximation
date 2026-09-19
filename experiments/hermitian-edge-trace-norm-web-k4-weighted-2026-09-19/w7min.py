# w7min.py SEED0 NSEEDS STARTS [WINDOW]: numerical upper bounds on c(G[W]) for a window W of C_14^4,
# given as comma-separated vertices (default 0,1,2,3,4,5,8); vertices are re-indexed 0..|W|-1 in order.
import sys, numpy as np
from scipy.optimize import minimize
WIN=[int(v) for v in (sys.argv[4] if len(sys.argv)>4 else '0,1,2,3,4,5,8').split(',')]; n=len(WIN)
E=[(a,b) for a in range(n) for b in range(a+1,n) if min((WIN[a]-WIN[b])%14,(WIN[b]-WIN[a])%14)<=4]; m=len(E)
I=np.array([e[0] for e in E]); J=np.array([e[1] for e in E])
def mat(x):
    C=np.zeros((n,n),complex); v=(1+x[:m]**2)*np.exp(1j*x[m:]); C[I,J]=v; C[J,I]=np.conj(v); return C
def fg(x):
    C=mat(x); w,U=np.linalg.eigh(C); S=(U*np.sign(w))@U.conj().T
    G=S[J,I]  # d||C||/dC_ij (real part pairing): d = 2 Re(conj? ) ; use d/dv of tr(S C) = 2 Re(S_ji v)
    v=(1+x[:m]**2)*np.exp(1j*x[m:])
    dv_dt=2*x[:m]*np.exp(1j*x[m:]); dv_dp=1j*v
    g=np.concatenate([2*np.real(G*dv_dt),2*np.real(G*dv_dp)])
    return np.abs(w).sum(),g
if __name__=="__main__":
    s0,ns,st=map(int,sys.argv[1:4]); print('window',WIN,'edges',m,flush=True)
    for seed in range(s0,s0+ns):
        rng=np.random.default_rng(seed); best=(1e9,None)
        for r in range(st):
            x0=np.concatenate([rng.normal(0,.3,m),rng.uniform(0,2*np.pi,m)])
            res=minimize(fg,x0,jac=True,method='BFGS',options={'maxiter':3000,'gtol':1e-10})
            res=minimize(lambda x:fg(x)[0],res.x,method='Nelder-Mead',options={'maxiter':6000,'xatol':1e-10,'fatol':1e-12})
            if res.fun<best[0]: best=(res.fun,res.x)
        C=mat(best[1]); mu=np.abs(C[I,J]).min(); C=C/min(mu,1)
        print("seed",seed,"c<= %.6f"%np.abs(np.linalg.eigvalsh(C)).sum(),"moduli",np.round(np.abs(C[I,J]),4).tolist(),flush=True)
        
