# rotation-type second-order bound prototype: Z = Z0 + D1 - 1/2 Z0 D1^2 (Z^2 = I + D1^4/4)
import numpy as np, math, sys
from so2 import *
def realform(fun):
    # quadratic form of fun(v) (v complex NF-vector) as real 2NF x 2NF symmetric matrix via polarisation
    n=2*NF; B=np.eye(n); Q=np.zeros((n,n))
    def vv(x): return x[:NF]+1j*x[NF:]
    f0=[fun(vv(B[a])) for a in range(n)]
    for a in range(n):
        Q[a,a]=f0[a]
        for b in range(a+1,n): Q[a,b]=Q[b,a]=(fun(vv(B[a]+B[b]))-f0[a]-f0[b])/2
    return Q
def so3bound(c,h,alpha=1.0):
    K0=Kmat(c); lam,U=np.linalg.eigh(K0); sg=np.sign(lam); Z0=(U*sg)@U.conj().T; aK=(U*np.abs(lam))@U.conj().T
    L=np.zeros((M,M))
    for a in range(M):
        for b in range(M):
            if sg[a]!=sg[b]: L[a,b]=2/(abs(lam[a])+abs(lam[b]))
    def dsign(X): return U@((U.conj().T@X@U)*L)@U.conj().T
    Ef=[]
    for kk in range(NF):
        i,j=free[kk]; Ee=np.zeros((M,M),complex); Ee[i,j]=1; Ef.append(Ee)
    X=[alpha*dsign(E_+E_.T) for E_ in Ef]; Y=[alpha*dsign(1j*(E_-E_.T)) for E_ in Ef]
    def dK(v): return sum(v[e].real*(Ef[e]+Ef[e].T)+v[e].imag*1j*(Ef[e]-Ef[e].T) for e in range(NF))
    def D1(v): return sum(v[e].real*X[e]+v[e].imag*Y[e] for e in range(NF))
    def q(v): D=D1(v); return (np.trace(D@dK(v))-0.5*np.trace(D@D@aK)).real
    Q=realform(q)
    rho=2*math.sin(h/2); cc=np.exp(1j*np.asarray(c))
    lb=fc0=np.abs(lam).sum()
    Qd=Q.copy()
    for e in range(NF):
        i,j=free[e]; z=Z0[j,i]
        idx=[e,NF+e]; qe=Q[np.ix_(idx,idx)]
        def g(th):
            v=np.exp(1j*th)-cc[e]; x=np.array([v.real,v.imag]); return 2*(v*z).real+x@qe@x
        lb+=trigmin(g,c[e]-h,c[e]+h)
        for a in idx:
            for b in idx: Qd[a,b]=0
    lb+=min(0,np.linalg.eigvalsh(Qd)[0])*NF*rho*rho
    G=sum(X[e]@X[e]+Y[e]@Y[e] for e in range(NF)); g2=np.linalg.norm(G,2)*NF*rho*rho
    lb-=0.5*g2*2*NF*rho
    s=math.sqrt(1+0.25*g2*g2)
    return lb/s
if __name__=="__main__":
    rng=np.random.default_rng(1)
    for trial in range(4):
        c=list(rng.uniform(0,2*math.pi,NF)); K0=Kmat(c); lam,U=np.linalg.eigh(K0); Z0=(U*np.sign(lam))@U.conj().T
        out=[]
        for h in [0.2,0.4,0.7]:
            lin=linbound(Z0,c,h); so=max(so3bound(c,h,al) for al in (0.25,0.5,1.0))
            out.append("h%.1f lin %.2f so3 %.2f"%(h,lin,so))
        print("fc %.3f |"%np.abs(lam).sum(),"; ".join(out),flush=True)
