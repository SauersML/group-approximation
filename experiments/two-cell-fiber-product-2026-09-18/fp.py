# Fiber-product search for two w-cycles with proportional chains z1 = lam * z0 != 0.
# Gamma: folded graph on letters x,y (partial injections). Delta = component of Gamma x Gamma.
# Closed loops of Delta at (v0,v1) = words w reading closed loops at v0 and v1 in Gamma.
import sys, itertools
from fractions import Fraction as Fr

def rank(rows):
    M=[list(map(Fr,r)) for r in rows]; rk=0
    if not M: return 0
    ncol=len(M[0])
    for c in range(ncol):
        p=None
        for i in range(rk,len(M)):
            if M[i][c]!=0: p=i;break
        if p is None: continue
        M[rk],M[p]=M[p],M[rk]
        for i in range(len(M)):
            if i!=rk and M[i][c]!=0:
                f=M[i][c]/M[rk][c]
                M[i]=[a-f*b for a,b in zip(M[i],M[rk])]
        rk+=1
    return rk

def pinj(n):
    res=[]
    for k in range(n+1):
        for dom in itertools.combinations(range(n),k):
            for img in itertools.permutations(range(n),k):
                res.append(tuple(zip(dom,img)))
    return res

def components(n,edges):
    # product graph vertices (u,v); edges pairs (i,j) of Gamma-edges with same letter
    pe=[]
    for i,(a,b,l) in enumerate(edges):
        for j,(c,d,m) in enumerate(edges):
            if l==m: pe.append(((a,c),(b,d),i,j))
    adj={}
    for k,(s,t,i,j) in enumerate(pe):
        adj.setdefault(s,[]).append((k,t,1)); adj.setdefault(t,[]).append((k,s,-1))
    seen={}; comps=[]
    for s0 in adj:
        if s0 in seen: continue
        # BFS tree
        par={s0:None}; order=[s0]; q=[s0]
        while q:
            u=q.pop()
            for k,t,sg in adj[u]:
                if t not in par: par[t]=(k,u,sg); q.append(t); order.append(t)
        for u in order: seen[u]=len(comps)
        comps.append((s0,par))
    return pe,adj,comps

def path_to_root(par,u,E):
    z0=[0]*E; z1=[0]*E
    while par[u] is not None:
        k,p,sg=par[u]  # edge k traversed from p to u with sign sg meaning orientation
        yield k,sg
        u=p

def analyse(n,edges,lams):
    E=len(edges)
    pe,adj,comps=components(n,edges)
    hits=[]
    for s0,par in comps:
        if s0[0]==s0[1]: continue
        verts=set(par)
        # potential of each vertex: chain from root
        pot={}
        for u in par:
            z=[0]*(2*E)
            for k,sg in path_to_root(par,u,E):
                i,j=pe[k][2],pe[k][3]
                z[i]+=sg; z[E+j]+=sg
            pot[u]=z
        tree=set(v[0] for v in par.values() if v is not None)
        cyc=[]
        for k,(s,t,i,j) in enumerate(pe):
            if s in verts and k not in tree:
                z=[pot[s][m]-pot[t][m] for m in range(2*E)]
                z[i]+=1; z[E+j]+=1
                cyc.append(z)
        if len(cyc)<2: continue
        A=[c[:E] for c in cyc]; B=[c[E:] for c in cyc]
        full=rank(cyc)
        for lam in lams:
            r=rank([[b-lam*a for a,b in zip(ca,cb)] for ca,cb in zip(A,B)])
            if r<full: hits.append((s0,lam,len(cyc)))
    return hits

def graphs(n):
    P=pinj(n)
    for X in P:
        for Y in P:
            edges=[(a,b,0) for a,b in X]+[(a,b,1) for a,b in Y]
            deg=[0]*n
            for a,b,_ in edges: deg[a]+=1; deg[b]+=1
            if min(deg)<2: continue
            if len(edges)-n+1<2: continue
            # connected
            ad={i:set() for i in range(n)}
            for a,b,_ in edges: ad[a].add(b); ad[b].add(a)
            st=[0]; sn={0}
            while st:
                u=st.pop()
                for v in ad[u]:
                    if v not in sn: sn.add(v); st.append(v)
            if len(sn)<n: continue
            yield edges

if __name__=="__main__":
    n=int(sys.argv[1])
    lams=[Fr(2),Fr(3,2)]
    cnt=0;tot=0
    for edges in graphs(n):
        tot+=1
        h=analyse(n,edges,lams)
        if h:
            cnt+=1
            if cnt<=5: print(edges,h)
    print("graphs",tot,"with hits",cnt)
