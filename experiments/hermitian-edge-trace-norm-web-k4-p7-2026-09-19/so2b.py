# prototype (floats): compare linear fixed-Z box bound vs second-order bound on P_7^4 boxes
import numpy as np, math, sys
from scipy.optimize import minimize
w,k=7,4
E0=[(i,j) for i in range(w) for j in range(i+1,w) if j-i<=k]
M=w
adj={i:[] for i in range(M)}
for (i,j) in E0: adj[i].append(j); adj[j].append(i)
seen={0}; order=[0]; tree=[]
for u in order:
    for v in sorted(adj[u]):
        if v not in seen: seen.add(v); order.append(v); tree.append((min(u,v),max(u,v)))
free=[e for e in E0 if e not in tree]; E=tree+free; NS=len(tree); NF=len(free)
II=np.array([e[0] for e in E]); JJ=np.array([e[1] for e in E])
T=2.46; TARGET=6*math.sqrt(3)
def Kmat(th,t=None):
    t=np.ones(len(E)) if t is None else t
    ph=np.concatenate([np.zeros(NS),th]); C=np.zeros((M,M),complex); v=t*np.exp(1j*ph); C[II,JJ]=v; C[JJ,II]=np.conj(v); return C
def phi(g): return g if g>=0 else T*g
def cosmin(a,b):
    lo=min(math.cos(a),math.cos(b)); kk=math.ceil((a-math.pi)/(2*math.pi))
    if math.pi+2*math.pi*kk<=b: lo=-1.0
    return lo
def linbound(Z,c,h):
    s=0
    for kk,(i,j) in enumerate(E):
        z=Z[j,i]
        if kk<NS: s+=phi(2*z.real); continue
        a=np.angle(z); s+=phi(2*abs(z)*cosmin(c[kk-NS]+a-h,c[kk-NS]+a+h))
    return s
def trigmin(f,lo,hi,n=64):
    xs=np.linspace(lo,hi,n); return min(f(x) for x in xs)  # prototype: no remainder
def so2bound(c,h,alpha=1.0,Z0=None):
    K0=Kmat(c); lam,U=np.linalg.eigh(K0); sg=np.sign(lam)
    if Z0 is None: Z0=(U*sg)@U.conj().T
    # Daleckii-Krein divided difference of sign
    L=np.zeros((M,M))
    for a in range(M):
        for b in range(M):
            if sg[a]!=sg[b]: L[a,b]=2/(abs(lam[a])+abs(lam[b]))
    def dsign(X): return U@((U.conj().T@X@U)*L)@U.conj().T
    A=[]
    for kk in range(NF):
        i,j=free[kk]; Ee=np.zeros((M,M),complex); Ee[i,j]=1
        X=dsign(Ee+Ee.T); Y=dsign(1j*(Ee-Ee.T)); A.append(alpha*(X-1j*Y)/2)
    rho=[2*math.sin(h/2)]*NF
    cc=np.exp(1j*np.asarray(c))
    # N(u,1)=tr(Z0 K(c)) + sum_e 2Re(v_e(z_e+tr(A_e K0))) + 2Re(v_e^2 al_e + |v_e|^2 be_e) + cross
    const=np.trace(Z0@K0).real; lb=const
    for kk in range(NF):
        i,j=free[kk]; z=Z0[j,i]; l1=z+np.trace(A[kk]@K0); al=A[kk][j,i]; be=A[kk][i,j]
        ce=cc[kk]
        def g(th): v=np.exp(1j*th)-ce; return 2*(v*l1).real+2*(v*v*al+abs(v)**2*be).real
        lb+=trigmin(g,c[kk]-h,c[kk]+h)
    # cross terms as real quadratic form in (Re v, Im v)
    Q=np.zeros((2*NF,2*NF))
    for e in range(NF):
        for f in range(NF):
            if e==f: continue
            i,j=free[f]; al=A[e][j,i]; be=A[e][i,j]
            # 2Re(v_e v_f al + v_e conj(v_f) be) with v=x+iy
            # v_e v_f = (xe xf - ye yf) + i(xe yf + ye xf); v_e conj v_f = (xe xf + ye yf) + i(ye xf - xe yf)
            ar,ai=al.real,al.imag; br,bi=be.real,be.imag
            # real part of (P+iQ)(ar+i ai) = P ar - Q ai
            Q[e,f]+=2*(ar+br); Q[NF+e,NF+f]+=2*(-ar+br)
            Q[e,NF+f]+=2*(-ai-bi); Q[NF+e,f]+=2*(-ai+bi)
    Q=(Q+Q.T)/2; lmin=np.linalg.eigvalsh(Q)[0]
    cross_spec=min(0,lmin)*sum(r*r for r in rho)
    lb+=cross_spec
    # per-edge moduli penalty skipped in prototype (G_f>=0 assumed); normalisation
    G=sum((A[e]+A[e].conj().T)@(A[e]+A[e].conj().T)+(1j*(A[e]-A[e].conj().T))@(1j*(A[e]-A[e].conj().T)) for e in range(NF))
    D2sq=sum(r*r for r in rho)*np.linalg.norm(G,2)
    s=math.sqrt(1+D2sq)
    return lb/s, const, lb, s
def truemin(c,h,rest=3,seed=0):
    rng=np.random.default_rng(seed); best=1e9
    f=lambda th: np.abs(np.linalg.eigvalsh(Kmat(th))).sum()
    for r in range(rest):
        x0=np.asarray(c)+(rng.uniform(-h,h,NF) if r else 0)
        res=minimize(f,x0,method='L-BFGS-B',bounds=[(ci-h,ci+h) for ci in c]); best=min(best,res.fun)
    return best
if __name__=="__main__":
    rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1)
    for trial in range(int(sys.argv[2]) if len(sys.argv)>2 else 8):
        c=list(rng.uniform(0,2*math.pi,NF)); K0=Kmat(c); fc=np.abs(np.linalg.eigvalsh(K0)).sum()
        lam,U=np.linalg.eigh(K0); Z0=(U*np.sign(lam))@U.conj().T
        out=[]
        for h in [0.2,0.4,0.7,1.0]:
            lin=linbound(Z0,c,h); so=max(so2bound(c,h,al)[0] for al in (0.1,0.25,0.5,1.0)); tm=truemin(c,h,2)
            out.append("h%.1f lin %.2f so %.2f true %.2f"%(h,lin,so,tm))
        print("fc %.3f minabs %.3f |"%(fc,np.min(np.abs(lam))),"; ".join(out),flush=True)
