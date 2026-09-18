# Rigorous branch-and-bound lower bound  min ||C||_1 >= TARGET  over admissible C on a fixed graph H.
# (Admissible: Hermitian, zero diagonal, C_ij = 0 on non-edges, |C_ij| >= 1 on edges.)
# This is cliquebb.py (experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18) with the complete
# graph replaced by an arbitrary graph and the star replaced by a BFS spanning tree.
# Usage: python3 graphbb.py GRAPH TARGET T n0 [a_lo a_hi [checkpoint.pkl]]   (checkpoint makes runs resumable)
#   GRAPH: K<m> (complete graph), or AH<n>:<v1>,<v2>,... (the subgraph of the odd antihole C_n-bar
#          induced on the listed vertices; i~j iff (i-j) mod n is not in {0,1,n-1}).
#   The first free phase ranges over [a_lo, a_hi] (default [0, 2pi]); the others over [0, 2pi].
# Gauge: a diagonal unitary makes every spanning-tree entry real and positive; the other entries
# K_ij = t_ij e^{i th_ij} carry the free phases th.  If some |K_ij| > T then ||K||_1 >= 2|K_ij| > 2T >= TARGET
# (compression to a 2x2 principal submatrix).  Otherwise, for any Hermitian Z with -I < Z < I,
#   ||K||_1 >= tr(ZK) = sum_edges t_ij g_ij ,   g_ij = 2 Re(Z_ji e^{i th_ij}),
# and min over t in [1,T] of t g is g (g >= 0) or T g (g < 0).  The bound is separable in the edges, so its
# minimum over a box of phases is computed edge by edge (exact cosine range, outward padding).
# Z: SDP dual optimum at the box centre, scaled by 1-1e-6, rounded to Gaussian rationals (denominator 2^30);
# -I < Z < I is checked exactly (Fraction pivots of I -+ Z).  Boxes are bisected until the bound is >= TARGET.
import numpy as np, cvxpy as cp, sys, math, time, itertools
from fractions import Fraction as Fr
def parse(g):
    if g[0]=='K':
        m=int(g[1:]); return m,[(i,j) for i in range(m) for j in range(i+1,m)]
    n,vs=g[2:].split(':'); n=int(n); S=[int(v) for v in vs.split(',')]
    E=[(a,b) for a in range(len(S)) for b in range(a+1,len(S)) if (S[a]-S[b])%n not in (0,1,n-1)]
    return len(S),E
GRAPH=sys.argv[1]; TARGET=float(sys.argv[2]); T=float(sys.argv[3]); n0=int(sys.argv[4])
assert 2*T>=TARGET
M,E0=parse(GRAPH)
# BFS spanning tree from vertex 0
adj={i:[] for i in range(M)}
for (i,j) in E0: adj[i].append(j); adj[j].append(i)
seen={0}; order=[0]; tree=[]
for u in order:
    for v in sorted(adj[u]):
        if v not in seen: seen.add(v); order.append(v); tree.append((min(u,v),max(u,v)))
assert len(seen)==M, "graph not connected"
E=tree+[e for e in E0 if e not in tree]
NS=len(tree); NF=len(E)-NS
PAD=1e-12
def up(x): return x+abs(x)*PAD+1e-14
def dn(x): return x-abs(x)*PAD-1e-14
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
DEN=2**30
def cfr(z): return (Fr(round(z.real*DEN),DEN),Fr(round(z.imag*DEN),DEN))
def cmul(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def csub(a,b): return (a[0]-b[0],a[1]-b[1])
def cdiv(a,b):
    d=b[0]*b[0]+b[1]*b[1]; return ((a[0]*b[0]+a[1]*b[1])/d,(a[1]*b[0]-a[0]*b[1])/d)
def pd_exact(A):
    # Gaussian elimination without pivoting on a Hermitian matrix of complex Fractions:
    # all pivots > 0 <=> positive definite (pivots are ratios of leading principal minors).
    A=[row[:] for row in A]; n=len(A)
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
        for j in range(i): R[i][j]=(R[j][i][0],-R[j][i][1])
    one=Fr(1)
    Mm=[[(one-R[i][j][0] if i==j else -R[i][j][0], -R[i][j][1]) for j in range(M)] for i in range(M)]
    Mp=[[(one+R[i][j][0] if i==j else R[i][j][0], R[i][j][1]) for j in range(M)] for i in range(M)]
    if not (pd_exact(Mm) and pd_exact(Mp)): return None
    return np.array([[complex(float(R[i][j][0]),float(R[i][j][1])) for j in range(M)] for i in range(M)])
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
    lo_a,hi_a=(float(sys.argv[5]),float(sys.argv[6])) if len(sys.argv)>6 else (0.0,2*math.pi)
    t0=time.time(); stack=[]
    for idx in itertools.product(range(n0),repeat=NF):
        box=[]
        for d,i in enumerate(idx):
            lo,hi=(lo_a,hi_a) if d==0 else (0.0,2*math.pi)
            box.append((lo+(hi-lo)*i/n0, lo+(hi-lo)*(i+1)/n0))
        stack.append((tuple(box),None))
    closed=0; solves=0; minval=1e9; worst=None; minw=1e9; reused=0
    import pickle, os
    ck=sys.argv[7] if len(sys.argv)>7 else None
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
    print(GRAPH,"edges %d tree %d free phases %d TARGET %.7f T %.3f first phase in [%.6f,%.6f]: ALL CLOSED  boxes %d (reused parent Z %d)  solves %d  min center value %.6f at %s  smallest half-width %.2e  time %.0fs"%(len(E),NS,NF,TARGET,T,lo_a,hi_a,closed,reused,solves,minval,[round(u,4) for u in (worst or [])],minw,time.time()-t0),flush=True)
