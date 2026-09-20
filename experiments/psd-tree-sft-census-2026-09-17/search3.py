import itertools, sys
import numpy as np
from scipy.optimize import linprog
n=int(sys.argv[1]) if len(sys.argv)>1 else 3
N=n*n
def mats():
    for bits in range(1<<N):
        M=np.array([(bits>>k)&1 for k in range(N)],dtype=np.int64).reshape(n,n)
        if M.sum(1).min()>0 and M.sum(0).min()>0:
            yield bits,M
def primitive(M):
    P=np.eye(n,dtype=np.int64);
    for k in range(1,(n-1)**2+2):
        P=(P@M>0).astype(np.int64)
        if P.min()>0: return True
    return False
ess=[(b,M) for b,M in mats() if primitive(M)]
print("primitive essential:",len(ess))
def cones_meet(Ma,Mb):
    # variables: m^a on edges of Ma, m^b on edges of Mb, n_i
    ea=list(zip(*np.nonzero(Ma))); eb=list(zip(*np.nonzero(Mb)))
    nv=len(ea)+len(eb)+n
    Aeq=[];beq=[]
    for (edges,off) in ((ea,0),(eb,len(ea))):
        for i in range(n):
            row=np.zeros(nv);
            for t,(u,v) in enumerate(edges):
                if u==i: row[off+t]+=1
            row[len(ea)+len(eb)+i]-=1; Aeq.append(row); beq.append(0)
            row=np.zeros(nv)
            for t,(u,v) in enumerate(edges):
                if v==i: row[off+t]+=1
            row[len(ea)+len(eb)+i]-=1; Aeq.append(row); beq.append(0)
    row=np.zeros(nv); row[len(ea)+len(eb):]=1; Aeq.append(row); beq.append(1)
    r=linprog(np.zeros(nv),A_eq=np.array(Aeq),b_eq=beq,bounds=[(0,None)]*nv,method='highs')
    return r.status==0
def rel(M): return frozenset(zip(*np.nonzero(M)))
def path_ok(Ma,Mb,cap=200):
    E={'a':rel(Ma),'A':rel(Ma.T),'b':rel(Mb),'B':rel(Mb.T)}
    inv={'a':'A','A':'a','b':'B','B':'b'}
    full=frozenset((i,j) for i in range(n) for j in range(n))
    succ={}
    for e in E:
        s={}
        for (i,j) in E[e]: s.setdefault(i,set()).add(j)
        succ[e]=s
    def mul(R,e):
        return frozenset((i,k) for (i,j) in R for k in succ[e].get(j,()))
    # graph of nonfull states; check acyclic
    start=[(E[e],e) for e in E if E[e]!=full]
    graph={}; stack=list(start)
    while stack:
        s=stack.pop()
        if s in graph: continue
        R,e=s; out=[]
        for f in E:
            if f==inv[e]: continue
            t=(mul(R,f),f)
            if t[0]!=full: out.append(t); stack.append(t)
        graph[s]=out
    # cycle detection
    color={}
    def dfs(u):
        color[u]=1
        for v in graph[u]:
            c=color.get(v,0)
            if c==1: return True
            if c==0 and dfs(v): return True
        color[u]=2; return False
    sys.setrecursionlimit(100000)
    for s in graph:
        if color.get(s,0)==0 and dfs(s): return False
    return True
cnt_nocone=0; hits=[]
for (ba,Ma) in ess:
    for (bb,Mb) in ess:
        if cones_meet(Ma,Mb): continue
        cnt_nocone+=1
        if path_ok(Ma,Mb):
            hits.append((ba,bb))
print("pairs with disjoint cones:",cnt_nocone)
print("of which path criterion holds:",len(hits))
for h in hits[:20]: print(h)
