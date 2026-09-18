# min over edge-supported Hermitian C (|C_e|>=1) of ||D_a C D_a||_1 / (sqrt3 (sum a - alpha_a))
import numpy as np, itertools, sys
from scipy.optimize import minimize
def alpha_w(adj,w):
    n=len(w); best=0
    for mask in range(1<<n):
        ok=True; s=0
        for i in range(n):
            if mask>>i&1:
                s+=w[i]
                for j in range(i+1,n):
                    if mask>>j&1 and adj[i][j]: ok=False;break
            if not ok: break
        if ok: best=max(best,s)
    return best
def fmin(adj,a,starts=20,seed=0,unimod=False):
    rng=np.random.default_rng(seed); n=len(a)
    E=[(i,j) for i in range(n) for j in range(i+1,n) if adj[i][j]]
    I=np.array([e[0] for e in E]); J=np.array([e[1] for e in E]); ne=len(E)
    sq=np.sqrt(np.array(a,float)); g=sq[I]*sq[J]
    def f(x):
        s=x[:ne]*(0 if unimod else 1); ph=x[ne:]
        c=(1+s**2)*np.exp(1j*ph)*g
        M=np.zeros((n,n),complex); M[I,J]=c; M[J,I]=np.conj(c)
        lam,V=np.linalg.eigh(M); S=(V*np.sign(lam))@V.conj().T
        G=S[J,I]
        gs=2*np.real(G*2*s*np.exp(1j*ph)*g)*(0 if unimod else 1); gph=2*np.real(G*1j*c)
        return np.abs(lam).sum(),np.concatenate([gs,gph])
    best=None
    for t in range(starts):
        x0=np.concatenate([rng.normal(0,0.3,ne),rng.uniform(0,2*np.pi,ne)])
        r=minimize(f,x0,jac=True,method='L-BFGS-B',options={'maxiter':4000})
        if best is None or r.fun<best.fun: best=r
    al=alpha_w(adj,a)
    return best.fun, best.fun/(np.sqrt(3)*(sum(a)-al)), al
def cyc(n): return [[1 if (j-i)%n in (1,n-1) else 0 for j in range(n)] for i in range(n)]
def comp(adj): n=len(adj); return [[0 if i==j else 1-adj[i][j] for j in range(n)] for i in range(n)]
def wheel(n): # rim C_n + hub
    A=cyc(n); A=[r+[1] for r in A]; A.append([1]*n+[0]); return A
def web(n,k): # W(n,k): i~j iff circular dist <= k (complement-convention: C_n^k)
    return [[1 if 0<min((j-i)%n,(i-j)%n)<=k else 0 for j in range(n)] for i in range(n)]
if __name__=="__main__":
    tests=[("C5",cyc(5),[1]*5),("C7",cyc(7),[1]*7),("antihole C7bar",comp(cyc(7)),[1]*7),
           ("antihole C9bar",comp(cyc(9)),[1]*9),("wheel W5",wheel(5),[1]*5+[2]),("wheel W7",wheel(7),[1]*7+[3]),
           ("web C8^2 (a=1)",web(8,2),[1]*8),("web C11^3",web(11,3),[1]*11),("C7^2",web(7,2),[1]*7),("C10^3",web(10,3),[1]*10)]
    for name,A,a in tests:
        v,r,al=fmin(A,a,starts=int(sys.argv[1]) if len(sys.argv)>1 else 12)
        print("%-16s n=%d alpha=%g  min=%.4f  need=%.4f ratio=%.4f"%(name,len(a),al,v,np.sqrt(3)*(sum(a)-al),r),flush=True)
