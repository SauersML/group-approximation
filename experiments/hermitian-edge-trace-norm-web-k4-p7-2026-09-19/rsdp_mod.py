import numpy as np, math, scipy.sparse as sp, clarabel
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
                bI.append(1.0 if row==col else 0.0); r+=1
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

