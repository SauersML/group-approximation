# wdens.py WINDOW STARTS w_0,...,w_{k-1}: numerical upper bound on the weighted value
#   c(G[W], w) = min ||C||_1 over Hermitian C on G[W] (zero diagonal, zero off edges) with |C_ij| >= sqrt(w_i w_j),
# and the density c(G[W], w) / sum(w).  G[W] is the subgraph of C_14^4 induced on WINDOW (comma-separated).
import sys, numpy as np
from scipy.optimize import minimize
def setup(WIN,N=14):
    n=len(WIN); E=[(a,b) for a in range(n) for b in range(a+1,n) if min((WIN[a]-WIN[b])%N,(WIN[b]-WIN[a])%N)<=4]
    return n,E
def cw(WIN,w,starts,seed=0,x0s=()):
    n,E=setup(WIN); m=len(E); I=np.array([e[0] for e in E]); J=np.array([e[1] for e in E])
    s=np.sqrt(np.array(w)[I]*np.array(w)[J])
    def fg(x):
        v=s*(1+x[:m]**2)*np.exp(1j*x[m:]); C=np.zeros((n,n),complex); C[I,J]=v; C[J,I]=np.conj(v)
        lam,U=np.linalg.eigh(C); S=(U*np.sign(lam))@U.conj().T; G=S[J,I]
        dv_dt=s*2*x[:m]*np.exp(1j*x[m:]); dv_dp=1j*v
        return np.abs(lam).sum(),np.concatenate([2*np.real(G*dv_dt),2*np.real(G*dv_dp)])
    rng=np.random.default_rng(seed); best=(1e9,None)
    inits=list(x0s)+[np.concatenate([rng.normal(0,.3,m),rng.uniform(0,2*np.pi,m)]) for _ in range(starts)]
    for x0 in inits:
        r=minimize(fg,x0,jac=True,method='BFGS',options={'maxiter':3000,'gtol':1e-10})
        if r.fun<best[0]: best=(r.fun,r.x)
    return best
if __name__=="__main__":
    WIN=[int(v) for v in sys.argv[1].split(',')]; st=int(sys.argv[2]); w=[float(v) for v in sys.argv[3].split(',')]
    c,x=cw(WIN,w,st); print("W",WIN,"w",w,"c<= %.6f density %.6f"%(c,c/sum(w)))
