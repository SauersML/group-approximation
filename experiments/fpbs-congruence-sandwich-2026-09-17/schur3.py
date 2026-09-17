# Bellman-Schur lower bound for p_{2->2} on Cay(F2 x Z, S_rig).
# Walk class: no revisit within the last L steps; chord factor (1-p)^c with chords to the last L positions.
# Weight phi = 3^{-beta/2} for a horofunction beta on the tree F2; state = (window, up-letter at current vertex).
import sys, itertools, math, time
import numpy as np
def build_geometry(L, D={1:[0,1,3],2:[0,1,4]}, vertical=((0,1),(0,-1))):
    G=[]
    for l,ks in D.items():
        for k in ks: G.append((l,k)); G.append((-l,-k))
    G+=list(vertical)
    def mul(v,g):
        w,n=v; l,k=g
        if l==0: return (w,n+k)
        if w and w[-1]==-l: return (w[:-1],n+k)
        return (w+(l,),n+k)
    Sgrp=set(mul(((),0),g) for g in G)
    def rel(a,b):
        wa,na=a; wb,nb=b; i=0
        while i<len(wa) and i<len(wb) and wa[i]==wb[i]: i+=1
        return (tuple(-x for x in reversed(wa[i:]))+wb[i:], nb-na)
    wins=[()]; posd={():[((),0)]}; level=[()]
    for t in range(L):
        new=[]
        for w in level:
            P=posd[w]
            for gi,g in enumerate(G):
                q=mul(P[-1],g)
                if q in P: continue
                nw=w+(gi,); posd[nw]=P+[q]; new.append(nw)
        wins+=new; level=new
    widx={w:i for i,w in enumerate(wins)}
    src=[];gis=[];dst=[];chd=[]
    for w in wins:
        P=posd[w]; cur=P[-1]; i=widx[w]
        for gi,g in enumerate(G):
            q=mul(cur,g)
            if q in P: continue
            c=sum(1 for x in P[:-1] if rel(x,q) in Sgrp)
            nw=w+(gi,)
            if len(nw)>L: nw=nw[1:]
            src.append(i); gis.append(gi); dst.append(widx[nw]); chd.append(c)
    return G,len(wins),np.array(src),np.array(gis),np.array(dst),np.array(chd)
def certify(G,NW,src,gis,dst,chd,p,iters=400,v0=None):
    letters=[1,-1,2,-2]; li={1:0,-1:1,2:2,-2:3}
    lg=np.array([G[g][0] for g in gis])
    wt=p*(1-p)**chd
    s3=math.sqrt(3)
    FS=[];FD=[];FW=[];US=[];UD=[];UW=[]
    for u in letters:
        S=src*4+li[u]
        vert=lg==0; up=lg==u; down=(lg!=0)&(lg!=u)
        FS.append(S[vert]); FD.append(dst[vert]*4+li[u]); FW.append(wt[vert])
        dl=np.array([li.get(-x,0) for x in lg[down]])
        FS.append(S[down]); FD.append(dst[down]*4+dl); FW.append(wt[down]/s3)
        others=[li[u2] for u2 in letters if u2!=-u]
        US.append(S[up]); UD.append(dst[up][:,None]*4+np.array(others)[None,:]); UW.append(wt[up]*s3)
    FS=np.concatenate(FS);FD=np.concatenate(FD);FW=np.concatenate(FW)
    US=np.concatenate(US);UD=np.concatenate(UD);UW=np.concatenate(UW)
    n=NW*4
    def T(v): return np.bincount(FS,FW*v[FD],minlength=n)+np.bincount(US,UW*v[UD].max(axis=1),minlength=n)
    v=np.ones(n) if v0 is None else v0.copy()
    for it in range(iters):
        nv=T(v); v=np.maximum(nv/nv.max(),1e-6)
    r=T(v)/v
    return r.max(), v
if __name__=='__main__':
    L=int(sys.argv[1]); t=time.time()
    geo=build_geometry(L); print('L',L,'windows',geo[1],'transitions',len(geo[2]),time.time()-t,flush=True)
    v=None
    for p in map(float,sys.argv[2:]):
        C,v=certify(*geo,p,v0=v); print('L',L,'p',p,'C_cert',C,time.time()-t,flush=True)
