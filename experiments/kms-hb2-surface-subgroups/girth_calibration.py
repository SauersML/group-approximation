import sys
from collections import deque
def run(P):
    def mul(A,B): return tuple(sum(A[4*r+k]*B[4*k+c] for k in range(4))%P for r in range(4) for c in range(4))
    I=tuple(int(r==c) for r in range(4) for c in range(4))
    def U(ents):
        M=list(I)
        for i,j,v in ents: M[4*i+j]=(M[4*i+j]+v)%P
        return tuple(M)
    A=U([(0,3,1),(1,2,1)]); B=U([(1,0,1),(2,3,-1)]); C=U([(3,1,1)])
    GEN={0:C,1:A,2:B}; PAIR={0:(1,2),1:(0,2),2:(0,1)}
    out=[]
    for i in range(3):
        j,k=PAIR[i]; gj,gk=GEN[j],GEN[k]
        elems=[I]; idx={I:0}; q=0
        while q<len(elems):
            g=elems[q]; q+=1
            for h in (gj,gk):
                x=mul(g,h)
                if x not in idx: idx[x]=len(elems); elems.append(x)
        n=len(elems)
        def pows(g):
            L=[I]
            for _ in range(P-1): L.append(mul(L[-1],g))
            return L
        pj,pk=pows(gj),pows(gk)
        # coset ids: left cosets x<g>
        cj={}; ck={}
        for x in elems:
            if x not in cj:
                cid=len(set(cj.values()))
                for e in pj: cj[mul(x,e)]=cid
            if x not in ck:
                cid=len(set(ck.values()))
                for e in pk: ck[mul(x,e)]=cid
        nj=len(set(cj.values())); nk=len(set(ck.values()))
        adj=[[] for _ in range(nj+nk)]
        for x in elems:
            u=cj[x]; v=nj+ck[x]; adj[u].append(v); adj[v].append(u)
        # girth via BFS from vertex 0 (vertex-transitive on each side) and from nj
        best=10**9
        for s in (0,nj):
            dist={s:0}; par={s:-1}; dq=deque([s])
            while dq:
                u=dq.popleft()
                for w in adj[u]:
                    if w not in dist: dist[w]=dist[u]+1; par[w]=u; dq.append(w)
                    elif par[u]!=w: best=min(best,dist[u]+dist[w]+1)
        out.append((i,n,nj,nk,best))
    print('p',P,[f'type{i}: |X|={n} cosets {nj}+{nk} girth {g}' for i,n,nj,nk,g in out])
for P in map(int,sys.argv[1:]): run(P)
