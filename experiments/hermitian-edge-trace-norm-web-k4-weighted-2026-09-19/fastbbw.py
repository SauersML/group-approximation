# fastbbw.py: VERTEX-WEIGHTED version of fastbb.py (w9-078), lane w11-078, 2026-09-19.
# It certifies  c(H, w) >= TARGET, where for weights w_i > 0 (exact rationals)
#   c(H, w) = min ||C||_1 over Hermitian C on H (zero diagonal, zero on non-edges) with |C_ij| >= sqrt(w_i w_j) on edges.
# Write C = D^(1/2) K D^(1/2), D = diag(w); then K is admissible (|K_ij| >= 1).  Changes against fastbb.py:
#   * the dual matrix is Z' = D^(1/2) Z D^(1/2) with -D < Z' < D (exact Fraction pivots of D - Z', D + Z'); then
#     Z = D^(-1/2) Z' D^(-1/2) has -I < Z < I and ||C||_1 >= tr(Z C) = tr(Z' K) = sum_e t_e g_e as before;
#   * the modulus cut is per edge: if |K_ij| > T_ij then pinching gives ||C||_1 >= 2 T_ij sqrt(w_i w_j) + MCUT_ij,
#     MCUT_ij = best packing of the other vertices into disjoint edges ab (value 2 sqrt(w_a w_b)) and triangles abc
#     (value 2 sqrt(w_a w_b + w_b w_c + w_a w_c)), and T_ij is chosen with 2 T_ij sqrt(w_i w_j) + MCUT_ij >= TARGET;
#   * the centre value and the centre sign candidate use D^(1/2) K D^(1/2).
#   * (search only) a full circle is split into FULLSPLIT pieces (env, default 4; fastbb.py uses 3).
# Usage: fastbbw.py GRAPH TARGET WEIGHTS a_lo a_hi checkpoint.pkl   (WEIGHTS: comma-separated rationals p/q)
# ---- the rest of this header is that of fastbb.py ----
# fastbb.py: adaptive, warm-candidate version of
#   experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/graphbb_r.py
# Rigorous branch-and-bound lower bound  min ||C||_1 >= TARGET  over admissible C on a fixed graph H
# (Hermitian, zero diagonal, C_ij = 0 on non-edges, |C_ij| >= 1 on edges).
#
# The CERTIFICATE is unchanged from graphbb.py / graphbb_r.py:
#   * gauge: a diagonal unitary makes the spanning-tree entries real positive; the other entries
#     K_ij = t_ij e^{i th_ij} carry the free phases th;
#   * if some |K_ij| > T then ||K||_1 >= 2T + MCUT >= TARGET (pinching; MCUT below);
#   * otherwise, for a Gaussian-rational Hermitian Z with I - Z and I + Z positive definite (exact Fraction
#     pivots), ||K||_1 >= tr(ZK) = sum_e t_e g_e,  g_e = 2 Re(Z_ji e^{i th_e}), minimised edge by edge over
#     t_e in [1,T] and the phase box (exact cosine ranges, outward padding) -- function box_bound.
#   A box is closed only when box_bound(Zr, box) >= TARGET for an exactly checked rational Zr.
# What is new (only the SEARCH for Zr and the splitting rule; neither affects soundness):
#   1. candidates in order: the parent's Zr; sign(C(centre)) (the exact dual optimum at the centre);
#      the robust SDP of graphbb_r.py over the box.  The first that closes the box is used.
#   2. arcs of length >= pi are allowed: the robust SDP then forces Z_ji = 0 on that edge.
#   3. adaptive split: the phase whose arc costs box_bound the most (for the best Z at hand) is bisected.
#   4. checkpoint (pickle of the stack and counters) every CKEVERY solves; resumes from it.
# Usage: fastbb.py GRAPH TARGET T a_lo a_hi checkpoint.pkl      env: ROOT=<tree root> FIRST=<i>-<j>
import numpy as np, cvxpy as cp, sys, math, time, pickle, os
from fractions import Fraction as Fr
def parse(g):
    if g[0]=='K':
        m=int(g[1:]); return m,[(i,j) for i in range(m) for j in range(i+1,m)]
    head,vs=g[1:].split(':'); n,ds=head.split('/'); n=int(n); Dd=[int(v) for v in ds.split('.')]; S=[int(v) for v in vs.split(',')]
    E=[(a,b) for a in range(len(S)) for b in range(a+1,len(S)) if min((S[a]-S[b])%n,(S[b]-S[a])%n) in Dd]
    return len(S),E
GRAPH=sys.argv[1]; TARGET=float(sys.argv[2]); WSTR=sys.argv[3]
M,E0=parse(GRAPH)
WF=[Fr(v) for v in WSTR.split(',')]; assert len(WF)==M and all(v>0 for v in WF)
wf=[float(v) for v in WF]
# modulus cut: if |K_ij| = t > T then pinching into {i,j} and the rest gives ||K||_1 >= 2t + LB(rest), where LB(rest) is
# the best packing of the rest into vertex-disjoint edges (||.||_1 >= 2) and triangles (||.||_1 >= 2 sqrt3: a 3x3
# zero-diagonal Hermitian with |entries| >= 1 has sum lambda^2 >= 6 and trace 0, so ||.||_1^2 / 2 >= 6).
import itertools
ES=set(E0)
def adjq(a,b): return (min(a,b),max(a,b)) in ES
def pack(V):
    V=sorted(V)
    if len(V)<2: return 0.0
    v=V[0]; rest=V[1:]; best=pack(rest)
    for u in rest:
        if adjq(v,u): best=max(best,2.0*math.sqrt(wf[v]*wf[u])*(1-1e-12)+pack([x for x in rest if x!=u]))
    for u,w in itertools.combinations(rest,2):
        if adjq(v,u) and adjq(v,w) and adjq(u,w): best=max(best,2*math.sqrt(wf[v]*wf[u]+wf[u]*wf[w]+wf[v]*wf[w])*(1-1e-12)+pack([x for x in rest if x not in (u,w)]))
    return best
MCUTE={e:pack([x for x in range(M) if x not in e]) for e in E0}
TEd={e:max(1.0,(TARGET-MCUTE[e])/(2*math.sqrt(wf[e[0]]*wf[e[1]])*(1-1e-12))*(1+1e-9)) for e in E0}
for e in E0: assert 2*TEd[e]*math.sqrt(wf[e[0]]*wf[e[1]])*(1-1e-12)+MCUTE[e]>=TARGET*(1+1e-10), e
ROOT=int(os.environ.get('ROOT','0'))
adj={i:[] for i in range(M)}
for (i,j) in E0: adj[i].append(j); adj[j].append(i)
seen={ROOT}; order=[ROOT]; tree=[]
for u in order:
    for v in sorted(adj[u]):
        if v not in seen: seen.add(v); order.append(v); tree.append((min(u,v),max(u,v)))
assert len(seen)==M, "graph not connected"
free=[e for e in E0 if e not in tree]
if 'FIRST' in os.environ:
    a,b=map(int,os.environ['FIRST'].split('-')); f0=(min(a,b),max(a,b)); assert f0 in free
    free.remove(f0); free=[f0]+free
E=tree+free; NS=len(tree); NF=len(free); TE=[TEd[e] for e in E]; T=max(TE)
print("weights",WSTR,"per-edge T",{e:round(TEd[e],4) for e in E},flush=True)
FULLSPLIT=int(os.environ.get('FULLSPLIT','4'))
PAD=1e-12
def up(x): return x+abs(x)*PAD+1e-14
def dn(x): return x-abs(x)*PAD-1e-14
# ---- robust SDP (search only; its output is re-checked exactly, so solver accuracy does not matter) ----
# maximise sum_e s_e over Hermitian Z = X + iY with -I <= Z <= I, 0 <= s_e <= 2 Re(Z_ji e^{i th}) at both ends of
# the arc of edge e (on an arc of length < pi a sinusoid >= 0 at both ends is >= 0 on the arc with its minimum at
# an end); on arcs of length >= pi, Z_ji = 0.  Solved with Clarabel directly (real 2M x 2M form of the LMIs).
import scipy.sparse as sp, clarabel
# direct Clarabel robust SDP (search only).  Variables: X_ab (a<=b), Y_ab (a<b), s_e.
class RobustSDP:
    def __init__(self,M,E,NS):
        self.M=M; self.E=E; self.NS=NS
        self.ix={}; k=0
        for a in range(M):
            for b in range(a,M): self.ix[('X',a,b)]=k; k+=1
        for a in range(M):
            for b in range(a+1,M): self.ix[('Y',a,b)]=k; k+=1
        self.ns0=k; self.nv=k+len(E)
        # svec rows of R(Z)=[[X,-Y],[Y,X]] (2M x 2M), upper triangle column-major, offdiag * sqrt2
        N=2*M; rows=[];cols=[];vals=[]; bI=[]
        r=0; s2=math.sqrt(2)
        def Xc(a,b): a,b=min(a,b),max(a,b); return self.ix[('X',a,b)],1.0
        def Yc(a,b):
            if a==b: return None
            if a<b: return self.ix[('Y',a,b)],1.0
            return self.ix[('Y',b,a)],-1.0
        for col in range(N):
            for row in range(col+1):
                sc=1.0 if row==col else s2
                i,j=row%M,col%M; bi,bj=row//M,col//M
                if bi==bj: ent=Xc(i,j)
                elif bi==0 and bj==1:   # -Y_ij
                    e=Yc(i,j); ent=None if e is None else (e[0],-e[1])
                else:                   # Y_ij
                    ent=Yc(i,j)
                if ent is not None: rows.append(r); cols.append(ent[0]); vals.append(sc*ent[1])
                bI.append(wf[row%M] if row==col else 0.0); r+=1
        self.nsv=r
        self.Rsv=sp.csc_matrix((vals,(rows,cols)),shape=(r,self.nv))
        self.bI=np.array(bI)
        self.st=clarabel.DefaultSettings(); self.st.verbose=False
    def solve(self,box):
        M,E,NS=self.M,self.E,self.NS; ne=len(E)
        rz=[];cz=[];vz=[]; nz=0
        rl=[];cl=[];vl=[]; nl=0
        for k,(i,j) in enumerate(E):
            sk=self.ns0+k; xi=self.ix[('X',i,j)]; yi=self.ix[('Y',i,j)]
            rl.append(nl); cl.append(sk); vl.append(-1.0); nl+=1          # -s <= 0
            if k<NS: arcs=[0.0]
            else:
                lo,hi=box[k-NS]
                if hi-lo>=math.pi-1e-9:
                    rz+= [nz,nz+1]; cz+=[xi,yi]; vz+=[1.0,1.0]; nz+=2
                    rl.append(nl); cl.append(sk); vl.append(1.0); nl+=1   # s <= 0
                    continue
                arcs=[lo,hi]
            for th in arcs:
                rl+=[nl,nl,nl]; cl+=[sk,xi,yi]; vl+=[1.0,-2*math.cos(th),-2*math.sin(th)]; nl+=1
        blocks=[];b=[];cones=[]
        if nz: blocks.append(sp.csc_matrix((vz,(rz,cz)),shape=(nz,self.nv))); b.append(np.zeros(nz)); cones.append(clarabel.ZeroConeT(nz))
        blocks.append(sp.csc_matrix((vl,(rl,cl)),shape=(nl,self.nv))); b.append(np.zeros(nl)); cones.append(clarabel.NonnegativeConeT(nl))
        blocks+= [self.Rsv, -self.Rsv]; b+=[self.bI,self.bI]; cones+=[clarabel.PSDTriangleConeT(2*M),clarabel.PSDTriangleConeT(2*M)]
        A=sp.vstack(blocks).tocsc(); bb=np.concatenate(b)
        q=np.zeros(self.nv); q[self.ns0:]=-1.0
        P=sp.csc_matrix((self.nv,self.nv))
        sol=clarabel.DefaultSolver(P,q,A,bb,cones,self.st).solve()
        x=np.array(sol.x)
        Z=np.zeros((M,M),complex)
        for a in range(M):
            for c in range(a,M):
                Z[a,c]+=x[self.ix[('X',a,c)]]
                if c>a: Z[c,a]+=x[self.ix[('X',a,c)]]
        for a in range(M):
            for c in range(a+1,M):
                y=x[self.ix[('Y',a,c)]]; Z[a,c]+=1j*y; Z[c,a]-=1j*y
        return -sol.obj_val, Z, str(sol.status)

RS=RobustSDP(M,E,NS)
def solve_box(box):
    try:
        v,Z,stt=RS.solve(box)
        if not np.all(np.isfinite(Z)): return None,None
        return v,Z
    except Exception: return None,None
# ---- symmetry: env SYM="p<q1,q2,...;p'<q1',..." (edges as i-j).  u(th) = distance from th to pi Z, which is
# invariant under th -> -th and th -> th + pi.  A box is dropped if on it u_q < u_p everywhere for one condition.
# Which conditions are valid (their intersection with the first-phase range meets every orbit) is argued in README.
def uint(lo,hi):
    """range of u(th) = dist(th, pi Z) over [lo,hi]"""
    k0=math.floor(lo/math.pi); umin=0.0 if math.ceil(lo/math.pi)*math.pi<=hi else None
    def u(t): r=t-math.pi*math.floor(t/math.pi); return min(r,math.pi-r)
    ul,uh=u(lo),u(hi)
    if umin is None: umin=min(ul,uh)
    umax=math.pi/2 if math.ceil((lo-math.pi/2)/math.pi)*math.pi+math.pi/2<=hi else max(ul,uh)
    return umin,umax
SYM=[]
# a term is a signed sum of edge phases, e.g. "1.2+2.3-1.3" (tree edges have phase 0, i-j is accepted for i.j);
# with a star tree at the root r, the triangle phase of {r,i,j} is i.j and that of {i,j,k} is i.j+j.k-i.k.
if os.environ.get('SYM'):
    pos={e:k for k,e in enumerate(free)}
    def term(x):
        x=x.replace('-','~') if '.' not in x else x
        out=[]; sg=1; tok=''
        for ch in x+'+':
            if ch in '+-':
                if tok:
                    a,b=map(int,tok.replace('~','.').split('.')); e=(min(a,b),max(a,b))
                    if e in pos: out.append((pos[e],sg if a<b else -sg))
                    else: assert e in tree
                tok=''; sg=1 if ch=='+' else -1
            else: tok+=ch
        return out
    for c in os.environ['SYM'].split(';'):
        pp,qs=c.split('<'); SYM.append((term(pp),[term(q) for q in qs.split(',')]))
def tint(t,box):
    lo=hi=0.0
    for k,sg in t:
        a,b=box[k]
        if sg>0: lo+=a; hi+=b
        else: lo-=b; hi-=a
    return uint(lo,hi)
def sym_drop(box):
    for p_,qs in SYM:
        up_=tint(p_,box)[0]
        for q in qs:
            if tint(q,box)[1]<up_-1e-9: return True
    return False
# ---- exact certificate pieces (as in graphbb.py) ----
DEN=2**30
def cfr(z): return (Fr(round(z.real*DEN),DEN),Fr(round(z.imag*DEN),DEN))
def cmul(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def csub(a,b): return (a[0]-b[0],a[1]-b[1])
def cdiv(a,b):
    d=b[0]*b[0]+b[1]*b[1]; return ((a[0]*b[0]+a[1]*b[1])/d,(a[1]*b[0]-a[0]*b[1])/d)
def pd_exact(A):
    A=[row[:] for row in A]; n=len(A)
    for k in range(n):
        p=A[k][k]
        if p[0]<=0: return False
        for i in range(k+1,n):
            f=cdiv(A[i][k],p)
            for j in range(k,n): A[i][j]=csub(A[i][j],cmul(f,A[k][j]))
    return True
def round_Z(Z):
    """Gaussian-rational Hermitian rounding of (1-1e-6) Z; returns (float copy, exact matrix)."""
    Z=(Z+Z.conj().T)/2*(1-1e-6)
    R=[[cfr(Z[i,j]) for j in range(M)] for i in range(M)]
    for i in range(M):
        R[i][i]=(R[i][i][0],Fr(0))
        for j in range(i): R[i][j]=(R[j][i][0],-R[j][i][1])
    return np.array([[complex(float(R[i][j][0]),float(R[i][j][1])) for j in range(M)] for i in range(M)]),R
def check_exact(R):
    one=Fr(1)
    Mm=[[(WF[i]-R[i][j][0] if i==j else -R[i][j][0], -R[i][j][1]) for j in range(M)] for i in range(M)]
    Mp=[[(WF[i]+R[i][j][0] if i==j else R[i][j][0], R[i][j][1]) for j in range(M)] for i in range(M)]
    return pd_exact(Mm) and pd_exact(Mp)
def cos_min(a,b):
    lo=min(math.cos(a),math.cos(b))
    k=math.ceil((a-math.pi)/(2*math.pi))
    if math.pi+2*math.pi*k<=b: lo=-1.0
    return dn(lo)
def edge_terms(Zr,box):
    out=[]
    for k,(i,j) in enumerate(E):
        z=Zr[j,i]; r=abs(z); phi=math.atan2(z.imag,z.real)
        if k<NS: g=dn(2*z.real)
        else:
            lo,hi=box[k-NS]; cm=cos_min(lo+phi-1e-12,hi+phi+1e-12)
            g=dn(2*dn(r)*cm) if cm>=0 else dn(2*up(r)*cm)
        out.append(g if g>=0 else up(TE[k])*g)
    return out
def box_bound(Zr,box):
    s=0.0
    for v in edge_terms(Zr,box): s=dn(s+v)
    return s
DH=np.diag(np.sqrt(wf))
II=np.array([e[0] for e in E]); JJ=np.array([e[1] for e in E])
def centre_matrix(box):
    th=np.concatenate([np.zeros(NS),[(u[0]+u[1])/2 for u in box]])
    C=np.zeros((M,M),complex); C[II,JJ]=np.exp(1j*th); C[JJ,II]=np.conj(C[II,JJ]); return C
def split_dim(Zf,box):
    """phase whose arc costs box_bound the most, measured with Zf = sign(C(centre))."""
    best=-1.0; d=0
    for k in range(NF):
        i,j=E[NS+k]; z=Zf[j,i]; lo,hi=box[k]; c=(lo+hi)/2
        gc=2*(z*np.exp(1j*c)).real; gc=gc if gc>=0 else TE[NS+k]*gc
        cm=cos_min(lo+np.angle(z),hi+np.angle(z)); gm=2*abs(z)*cm; gm=gm if gm>=0 else TE[NS+k]*gm
        if gc-gm>best: best=gc-gm; d=k
    return d
def pieces(lo,hi):
    p=2 if hi-lo<2*(math.pi-0.05) else FULLSPLIT
    return [(lo+(hi-lo)*q/p, lo+(hi-lo)*(q+1)/p) for q in range(p)]
def make(Z):
    f,R=round_Z(Z); return {'f':f,'R':R,'ok':None}
def try_close(c,box):
    if box_bound(c['f'],box)<TARGET: return False
    if c['ok'] is None: c['ok']=check_exact(c['R'])
    return c['ok']
if __name__=="__main__":
    lo_a,hi_a=float(sys.argv[4]),float(sys.argv[5]); ck=sys.argv[6]
    CKEVERY=int(os.environ.get('CKEVERY','1000'))
    box0=tuple([(lo_a,hi_a)]+[(0.0,2*math.pi)]*(NF-1))
    V0=math.prod(u[1]-u[0] for u in box0)
    def vol(b): return math.prod(u[1]-u[0] for u in b)/V0   # progress only
    st={'stack':[(box0,None)],'closed':0,'solves':0,'bysign':0,'byparent':0,'bysdp':0,'minfc':1e9,'worst':None,'minw':1e9,'t':0.0,'maxdepth':0}
    if os.path.exists(ck):
        st=pickle.load(open(ck,'rb')); print("resumed",len(st['stack']),"boxes on stack",flush=True)
    t0=time.time()-st['t']; lastck=st['solves']
    def save():
        st['t']=time.time()-t0; pickle.dump(st,open(ck+'.tmp','wb')); os.replace(ck+'.tmp',ck)
    stack=st['stack']
    while stack:
        if st['solves']-lastck>=CKEVERY: save(); lastck=st['solves']
        box,par=stack.pop()
        if SYM and sym_drop(box): st['symdrop']=st.get('symdrop',0)+1; st['vol']=st.get('vol',0)+vol(box); continue
        if par is not None and try_close(par,box): st['closed']+=1; st['byparent']+=1; st['vol']=st.get('vol',0)+vol(box); continue
        C=DH@centre_matrix(box)@DH; w,U=np.linalg.eigh(C); fc=float(np.abs(w).sum())
        if fc<st['minfc']: st['minfc']=fc; st['worst']=[(u[0]+u[1])/2 for u in box]
        if fc<TARGET:
            print("FAIL: admissible C with ||C||_1 = %.9f < TARGET at centre"%fc,[(u[0]+u[1])/2 for u in box],flush=True); save(); sys.exit(1)
        Zc=DH@((U*np.sign(w))@U.conj().T)@DH
        cc=make(Zc)
        if try_close(cc,box): st['closed']+=1; st['bysign']+=1; st['vol']=st.get('vol',0)+vol(box); continue
        v,Z=solve_box(box); st['solves']+=1
        best=cc
        if Z is not None:
            cr=make(Z)
            if try_close(cr,box): st['closed']+=1; st['bysdp']+=1; st['vol']=st.get('vol',0)+vol(box); continue
            if box_bound(cr['f'],box)>box_bound(cc['f'],box): best=cr
        d=split_dim(Zc,box)
        w_=box[d][1]-box[d][0]
        if w_<1e-4: print("FAIL: tiny box",box,flush=True); save(); sys.exit(1)
        st['minw']=min(st['minw'],w_/2)
        for half in pieces(*box[d]):
            nb=list(box); nb[d]=half; stack.append((tuple(nb),best))
        if st['solves']%1000==0:
            print("solves",st['solves'],"closed",st['closed'],"(parent %d sign %d sdp %d)"%(st['byparent'],st['bysign'],st['bysdp']),"stack",len(stack),"minfc %.6f"%st['minfc'],"vol %.3e"%st.get('vol',0),"t %.0f"%(time.time()-t0),flush=True)
    st['stack']=[]; save()
    print(GRAPH,"edges %d tree %d (root %d) free phases %d first %s SYM %s TARGET %.7f weights %s max T %.3f first phase in [%.6f,%.6f]: ALL CLOSED  boxes %d (dropped by symmetry %d; parent Z %d, centre sign %d, robust SDP %d)  solves %d  min centre value %.6f at %s  smallest half-width %.2e  time %.0fs"%(len(E),NS,ROOT,NF,E[NS],os.environ.get('SYM','-'),TARGET,WSTR,T,lo_a,hi_a,st['closed'],st.get('symdrop',0),st['byparent'],st['bysign'],st['bysdp'],st['solves'],st['minfc'],[round(u,4) for u in (st['worst'] or [])],st['minw'],time.time()-t0),flush=True)
