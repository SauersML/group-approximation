# vbb.py: vectorised branch-and-bound lower bound  min ||K||_1 >= TARGET  over admissible K on P_w^k
# (prototype; same certificate as fastbb.py: gauge-fixed tree, pinching cut |K_e| > T, and for each box a
# Hermitian Z with ||Z|| <= nb (rigorous float bound), ||K||_1 >= tr(ZK)/nb >= box_bound/nb).
import numpy as np, math, sys, time, itertools
w=int(sys.argv[1]); k=int(sys.argv[2]); TARGET=float(sys.argv[3]); lo1=float(sys.argv[4]); hi1=float(sys.argv[5])
MAXB=int(sys.argv[6]) if len(sys.argv)>6 else 10**12
E0=[(i,j) for i in range(w) for j in range(i+1,w) if j-i<=k]; M=w; ES=set(E0)
def adjq(a,b): return (min(a,b),max(a,b)) in ES
def pack(V):
    V=sorted(V)
    if len(V)<2: return 0.0
    v=V[0]; rest=V[1:]; best=pack(rest)
    for u in rest:
        if adjq(v,u): best=max(best,2.0+pack([x for x in rest if x!=u]))
    for u,x in itertools.combinations(rest,2):
        if adjq(v,u) and adjq(v,x) and adjq(u,x): best=max(best,2*math.sqrt(3)*(1-1e-12)+pack([y for y in rest if y not in (u,x)]))
    return best
MCUT=min(pack([x for x in range(M) if x not in e]) for e in E0)
T=(TARGET-MCUT)/2*(1-1e-12)
adj={i:[] for i in range(M)}
for (i,j) in E0: adj[i].append(j); adj[j].append(i)
seen={0}; order=[0]; tree=[]
for u in order:
    for v in sorted(adj[u]):
        if v not in seen: seen.add(v); order.append(v); tree.append((min(u,v),max(u,v)))
free=[e for e in E0 if e not in tree]; E=tree+free; NS=len(tree); NF=len(free)
TI=np.array([e[0] for e in tree]); TJ=np.array([e[1] for e in tree])
FI=np.array([e[0] for e in free]); FJ=np.array([e[1] for e in free])
print("graph P_%d^%d edges %d tree %s free %d MCUT %.6f T %.6f TARGET %.7f first phase %s in [%g,%g]"%(w,k,len(E),tree,NF,MCUT,T,TARGET,free[0],lo1,hi1),flush=True)
TWO_PI=2*math.pi
def cosmin(a,b):
    """vectorised min of cos on [a,b] (b-a <= 2pi), padded down"""
    c=np.minimum(np.cos(a),np.cos(b))
    kk=np.ceil((a-math.pi)/TWO_PI); hit=(math.pi+TWO_PI*kk)<=b
    return np.where(hit,-1.0,c)-1e-12
def normbound(Z):
    """upper bound on ||Z||_2 for Hermitian Z: max |eigenvalue| (LAPACK, backward stable) padded"""
    ev=np.linalg.eigvalsh(Z); return np.abs(ev).max(axis=1)*(1+1e-9)+1e-12
def bound(Z,lo,hi):
    """lower bound of tr(ZK) over the box and t in [1,T]^E, divided by a bound on ||Z||"""
    zt=Z[:,TJ,TI]; g=2*zt.real-1e-12
    s=np.where(g>=0,g,T*g).sum(axis=1)
    zf=Z[:,FJ,FI]; r=np.abs(zf); ph=np.angle(zf)
    cm=cosmin(lo+ph-1e-12,hi+ph+1e-12); g=2*r*cm
    g=np.where(g>=0,g*(1-1e-12),T*g*(1+1e-12))
    s=s+g.sum(axis=1)
    nb=normbound(Z)
    return np.where(s>0,s/nb*(1-1e-12),s), g
def centreK(lo,hi):
    B=lo.shape[0]; K=np.zeros((B,M,M),complex)
    K[:,TI,TJ]=1; K[:,TJ,TI]=1
    v=np.exp(1j*(lo+hi)/2); K[:,FI,FJ]=v; K[:,FJ,FI]=np.conj(v); return K
lo0=np.zeros(NF); hi0=np.full(NF,TWO_PI); lo0[0]=lo1; hi0[0]=hi1
stack_lo=[lo0[None]]; stack_hi=[hi0[None]]; stack_Z=[np.zeros((1,M,M),complex)]
import os; from rsdp_mod import RobustSDP; RS=RobustSDP(M,E,NS); HS=float(os.environ.get('HS','0.15'));WMIN=float(os.environ.get("WMIN","2e-3")); nsdp=[0,0]
PRINTN=int(os.environ.get("PRINTN","200000"))
BATCH=512; nbox=0; closed=0; minfc=1e9; t0=time.time(); minw=1e9; vol=0.0; V0=np.prod(hi0-lo0); last=0
while stack_lo:
    lo=stack_lo.pop(); hi=stack_hi.pop(); Zp=stack_Z.pop()
    nbox+=lo.shape[0]
    bp,_=bound(Zp,lo,hi)
    K=centreK(lo,hi); lam,U=np.linalg.eigh(K); fc=np.abs(lam).sum(axis=1)
    if fc.min()<TARGET: print("FAIL centre",fc.min(),(lo+hi)[fc.argmin()]/2,flush=True); sys.exit(1)
    minfc=min(minfc,fc.min())
    Zs=(U*np.sign(lam)[:,None,:])@np.conj(np.transpose(U,(0,2,1)))
    bs,gs=bound(Zs,lo,hi)
    ok=(bp>=TARGET)|(bs>=TARGET)
    cand=np.where(~ok & (((hi-lo).max(axis=1)<2*HS)|((hi-lo).min(axis=1)<WMIN)))[0]
    for q in cand:
        try:
            v,Zq,st_=RS.solve([(lo[q,e],hi[q,e]) for e in range(NF)]); nsdp[0]+=1
            if not np.all(np.isfinite(Zq)): continue
            Zq=(Zq+Zq.conj().T)/2
            bq,gq=bound(Zq[None],lo[q:q+1],hi[q:q+1])
            if bq[0]>=TARGET: ok[q]=True; nsdp[1]+=1
            elif bq[0]>bs[q]: Zs[q]=Zq; bs[q]=bq[0]; gs[q]=gq[0]
        except Exception: pass
    closed+=ok.sum(); vol+=np.prod(hi[ok]-lo[ok],axis=1).sum()/V0
    op=~ok
    if op.any():
        lo=lo[op]; hi=hi[op]; Zs=Zs[op]; Zp=Zp[op]; gs=gs[op]; bs=bs[op]; bp=bp[op]
        Zb=np.where((bs>=bp)[:,None,None],Zs,Zp)
        # split the free phase whose arc costs the most for the centre sign Z
        zf=Zs[:,FJ,FI]; c=(lo+hi)/2; gc=2*(zf*np.exp(1j*c)).real; gc=np.where(gc>=0,gc,T*gc)
        d=np.argmax(gc-gs,axis=1); ar=np.arange(lo.shape[0])
        wd=hi[ar,d]-lo[ar,d]; minw=min(minw,wd.min()/2)
        if wd.min()<1e-5:
            q=wd.argmin(); print("FAIL tiny box centre",list(np.round((lo[q]+hi[q])/2,5)),"w",list(np.round(hi[q]-lo[q],5)),"d",d[q],"gc",np.round(gc[q],4),"bs",bs[q],"g",np.round(gs[q],4),flush=True); sys.exit(1)
        mid=(lo[ar,d]+hi[ar,d])/2
        lo2=lo.copy(); hi1_=hi.copy(); hi1_[ar,d]=mid; lo2[ar,d]=mid
        L=np.concatenate([lo,lo2]); H=np.concatenate([hi1_,hi]); Zc=np.concatenate([Zb,Zb])
        for s0 in range(0,L.shape[0],BATCH):
            stack_lo.append(L[s0:s0+BATCH]); stack_hi.append(H[s0:s0+BATCH]); stack_Z.append(Zc[s0:s0+BATCH])
    if nbox-last>=PRINTN:
        last=nbox; print("sdp %d/%d boxes %d closed %d stack %d minfc %.6f minhalfw %.2e vol %.4e t %.0f"%(nsdp[0],nsdp[1],nbox,closed,sum(x.shape[0] for x in stack_lo),minfc,minw,vol,time.time()-t0),flush=True)
    if nbox>MAXB: print("STOP maxboxes vol %.4e"%vol,flush=True); sys.exit(2)
print("sdp solves %d closed-by-sdp %d"%tuple(nsdp)); print("ALL CLOSED boxes %d leaves %d minfc %.6f minhalfw %.3e t %.0f"%(nbox,closed,minfc,minw,time.time()-t0),flush=True)
