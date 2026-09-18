# Rigorous branch-and-bound proof of the clique inequality ||K||_1 >= sqrt3 (m-1) for m = 4, 5.
# Usage: python3 cliquebb.py m a_lo a_hi tag n0 [checkpoint.pkl]   (first free phase in [a_lo,a_hi], others in [0,2pi), n0^NF start grid)
# Gauge: a diagonal unitary makes K_1j = t_1j >= 1 real (star edges); the other m-1 choose 2 entries are
# K_ij = t_ij e^{i th_ij} with t_ij >= 1 and free phases th (the "free coordinates", NF of them).
# Symmetries: C -> -C (then conjugate by diag(-1,1,..,1)) shifts every free phase by pi, and C -> conj C
# negates them, so the first free phase may be restricted to [0, pi/2] (the m = 5 run does this).
# If some |K_ij| > T (T = 2.6 for m=4, 3.47 for m=5) then ||K||_1 >= 2|K_ij| > 2T > sqrt3 (m-1), by
# compressing to a 2x2 principal submatrix. Otherwise, for any Hermitian Z with -I <= Z <= I:
#   ||K||_1 >= tr(ZK) = sum_{i<j} t_ij g_ij,   g_ij = 2 Re(Z_ji e^{i th_ij}),
# and min over t in [1,T] of t g is g (g >= 0) or T g (g < 0). The bound is separable in the edges, so
# its minimum over a box of phases is computed exactly edge by edge (cos range, outward padding).
# Z comes from the SDP dual at the box centre, is rounded to Gaussian rationals (denominator 2^30) after
# scaling by 1 - 1e-6, and -I < Z < I is checked exactly (pivots of I -+ Z in exact Fractions).
# Boxes are bisected until the bound exceeds TARGET > sqrt3 (m-1).
import numpy as np, cvxpy as cp, sys, math, time, json
from fractions import Fraction as Fr
M=int(sys.argv[1])
E=[(i,j) for i in range(M) for j in range(i+1,M)]
NS=M-1; NF=len(E)-NS   # star edges (0,j) come first
T={4:2.6,5:3.47}[M]; TARGET={4:5.1961525,5:6.9282033}[M]  # 2T > TARGET > sqrt3 (M-1)
PAD=1e-12
def up(x): return x+abs(x)*PAD+1e-14
def dn(x): return x-abs(x)*PAD-1e-14
# ---- SDP with parameters
Zv=cp.Variable((M,M),hermitian=True)
P=[cp.Parameter(complex=True) for _ in E]
gexpr=[2*cp.real(Zv[j,i]*P[k]) for k,(i,j) in enumerate(E)]
prob=cp.Problem(cp.Maximize(sum(gexpr)),[np.eye(M)-Zv>>0,np.eye(M)+Zv>>0]+[g>=0 for g in gexpr])
def ph(x): return [0.0]*NS+list(x)
def solve(x):
    for k,t in enumerate(ph(x)): P[k].value=np.exp(1j*t)
    try: prob.solve(solver='CLARABEL')
    except Exception: prob.solve(solver='SCS',eps=1e-9)
    return prob.value, Zv.value
# ---- exact check of -I < Z < I
DEN=2**30
def cfr(z): return (Fr(round(z.real*DEN),DEN),Fr(round(z.imag*DEN),DEN))
def cmul(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def csub(a,b): return (a[0]-b[0],a[1]-b[1])
def cdiv(a,b):
    d=b[0]*b[0]+b[1]*b[1]; return ((a[0]*b[0]+a[1]*b[1])/d,(a[1]*b[0]-a[0]*b[1])/d)
def pd_exact(M):
    # Gaussian elimination without pivoting; M Hermitian (list of lists of complex fractions).
    # Pivots are the ratios of consecutive leading principal minors, so all pivots > 0 <=> PD.
    A=[row[:] for row in M]; n=len(A)
    for k in range(n):
        p=A[k][k]
        if p[0]<=0: return False
        for i in range(k+1,n):
            f=cdiv(A[i][k],p)
            for j in range(k,n): A[i][j]=csub(A[i][j],cmul(f,A[k][j]))
    return True
def rational_Z(Z):
    Z=(Z+Z.conj().T)/2*(1-1e-6)
    R=[[cfr(Z[i,j]) for j in range(M)] for i in range(M)]
    for i in range(M):
        R[i][i]=(R[i][i][0],Fr(0))
        for j in range(i): R[i][j]=(R[j][i][0],-R[j][i][1])  # exact Hermitian
    one=Fr(1)
    Mm=[[ (one-R[i][j][0] if i==j else -R[i][j][0], -R[i][j][1]) for j in range(M)] for i in range(M)]
    Mp=[[ (one+R[i][j][0] if i==j else R[i][j][0], R[i][j][1]) for j in range(M)] for i in range(M)]
    if not (pd_exact(Mm) and pd_exact(Mp)): return None
    return np.array([[complex(float(R[i][j][0]),float(R[i][j][1])) for j in range(M)] for i in range(M)])
# ---- rigorous lower bound of the certificate on a box
def cos_min(a,b):
    lo=min(math.cos(a),math.cos(b))
    k=math.ceil((a-math.pi)/(2*math.pi))
    if math.pi+2*math.pi*k<=b: lo=-1.0
    return dn(lo)
def box_bound(Zr,box):
    s=0.0
    for k,(i,j) in enumerate(E):
        z=Zr[j,i]; r=abs(z); phi=math.atan2(z.imag,z.real)
        if k<NS: g=dn(2*z.real)
        else:
            lo,hi=box[k-NS]; cm=cos_min(lo+phi-1e-12,hi+phi+1e-12)
            g=dn(2*dn(r)*cm) if cm>=0 else dn(2*up(r)*cm)
        s=dn(s+(g if g>=0 else T*g))
    return s
if __name__=="__main__":
    lo_a=float(sys.argv[2]); hi_a=float(sys.argv[3]); tag=sys.argv[4]; n0=int(sys.argv[5])
    import itertools
    t0=time.time(); stack=[]
    for idx in itertools.product(range(n0),repeat=NF):
        box=[]
        for d,i in enumerate(idx):
            lo,hi=(lo_a,hi_a) if d==0 else (0.0,2*math.pi)
            box.append((lo+(hi-lo)*i/n0, lo+(hi-lo)*(i+1)/n0))
        stack.append((tuple(box),None))
    closed=0; solves=0; minval=1e9; worst=None; minw=1e9; reused=0
    import pickle, os
    ck=sys.argv[6] if len(sys.argv)>6 else None
    if ck and os.path.exists(ck):
        stack,closed,solves,minval,worst,minw,reused,tprev=pickle.load(open(ck,"rb"))
        t0-=tprev; print("resumed",len(stack),"boxes on stack",flush=True)
    lastsave=time.time()
    while stack:
        if ck and time.time()-lastsave>60:
            pickle.dump((stack,closed,solves,minval,worst,minw,reused,time.time()-t0),open(ck+".tmp","wb")); os.replace(ck+".tmp",ck); lastsave=time.time()
        box,Zp=stack.pop()
        if Zp is not None and box_bound(Zp,box)>=TARGET: closed+=1; reused+=1; continue
        x=[(u[0]+u[1])/2 for u in box]
        v,Z=solve(x); solves+=1
        if v<minval: minval=v; worst=x
        Zr=rational_Z(Z) if Z is not None else None
        if Zr is not None and box_bound(Zr,box)>=TARGET: closed+=1; continue
        w=[u[1]-u[0] for u in box]; d=int(np.argmax(w)); minw=min(minw,w[d]/2)
        if w[d]<1e-4: print("FAIL: tiny box",box,v,flush=True); sys.exit(1)
        for half in ((box[d][0],x[d]),(x[d],box[d][1])):
            nb_=list(box); nb_[d]=half; stack.append((tuple(nb_),Zr))
        if solves%2000==0: print("solves",solves,"closed",closed,"stack",len(stack),"minval %.6f"%minval,"t %.0f"%(time.time()-t0),flush=True)
    if ck: pickle.dump(([],closed,solves,minval,worst,minw,reused,time.time()-t0),open(ck,"wb"))
    print(tag,"m=%d first phase in [%.6f,%.6f]: ALL CLOSED  boxes %d (reused parent Z %d)  solves %d  min center value %.6f at %s  smallest half-width %.2e  time %.0fs"%(M,lo_a,hi_a,closed,reused,solves,minval,[round(u,4) for u in worst],minw,time.time()-t0),flush=True)
