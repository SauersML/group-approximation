# wopt.py WINDOW ITERS STARTS: maximise the numerical density c(G[W], w)/sum(w) over vertex weights w > 0.
# At a maximiser with minimiser C, d c/d w_i = |C|_ii / w_i, so the weights satisfy w_i ∝ |C|_ii (w = diag|C|
# normalised).  We iterate w <- (1-s) w + s diag|C(w)|/rho, with C(w) found from a warm pool plus random starts.
import sys, numpy as np
from wdens import cw, setup
WIN=[int(v) for v in sys.argv[1].split(',')]; its=int(sys.argv[2]); st=int(sys.argv[3]); k=len(WIN)
n,E=setup(WIN); m=len(E); I=np.array([e[0] for e in E]); J=np.array([e[1] for e in E])
def absdiag(w,x):
    s=np.sqrt(w[I]*w[J]); v=s*(1+x[:m]**2)*np.exp(1j*x[m:]); C=np.zeros((n,n),complex); C[I,J]=v; C[J,I]=np.conj(v)
    lam,U=np.linalg.eigh(C); return np.real(np.diag((U*np.abs(lam))@U.conj().T))
w=np.ones(k); pool=[]; best=(0,None,None)
for it in range(its):
    c,x=cw(WIN,w,st,seed=it,x0s=pool); pool=[x]+pool[:4]; rho=c/w.sum(); d=absdiag(w,x)
    if rho>best[0]: best=(rho,w.copy(),x)
    print("it %d density %.6f c %.6f w %s  diag|C|/(rho w) %s"%(it,rho,c,np.round(w,4).tolist(),np.round(d/(rho*w),3).tolist()),flush=True)
    w=0.5*w+0.5*d/rho; w=w/w.max()
rho,w,x=best; c,_=cw(WIN,w,4*st,seed=777,x0s=[x]); print("best w",np.round(w,5).tolist(),"recheck c<= %.6f density %.6f"%(c,c/w.sum()),flush=True)
