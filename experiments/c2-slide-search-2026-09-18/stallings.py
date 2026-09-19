# Stallings folding in the fibre F(p,q,r,s) of G = F4 x| Z.
# S = <beta = bDB, k = eDDEdd>; beta has level -1, k level 0, so S cap F4 = < beta^n k beta^-n : n in Z >.
# Test T beta^2 in < beta^n k beta^-n : |n| <= N > for growing N (positive answer is exact).
import sys
from verify_unimodular import U1, G_, inv, tox, fox, fred, nf
class Graph:
    def __init__(s): s.e={0:{}}; s.n=1
    def add_loop(s,w):
        v=0
        for i,c in enumerate(w):
            if i==len(w)-1: t=0
            else: t=s.n; s.e[t]={}; s.n+=1
            s._edge(v,c,t); v=t
        s.fold()
    def _edge(s,u,c,v):
        s.e[u].setdefault(c,set()).add(v); s.e[v].setdefault(c.swapcase(),set()).add(u)
    def fold(s):
        ch=True
        while ch:
            ch=False
            for u in list(s.e):
                if u not in s.e: continue
                for c,vs in list(s.e[u].items()):
                    if len(vs)>1:
                        vs=sorted(vs); a=vs[0]
                        for b in vs[1:]: s._merge(a,b)
                        ch=True; break
                if ch: break
    def _merge(s,a,b):
        if a==b: return
        if b==0: a,b=b,a
        for c,vs in list(s.e[b].items()):
            for v in list(vs):
                s.e[v][c.swapcase()].discard(b)
                vv=a if v==b else v
                s._edge(a,c,vv)
        del s.e[b]
    def accepts(s,w):
        v=0
        for c in w:
            nx=s.e[v].get(c)
            if not nx: return False
            v=next(iter(nx))
        return v==0
    def rank(s):
        E=sum(len(vs) for d in s.e.values() for vs in d.values())//2
        return E-len(s.e)+1
if __name__=='__main__':
    idx=int(sys.argv[2]) if len(sys.argv)>2 else 1
    k='eDDEdd'; kA=k+'A'; beta=tox('bDB'); kx=tox(k)
    P=[fred(p+inv(tox('dEb'))) for s,p in fox(U1,'c')]
    T=fred(inv(tox(kA))+G_+inv(P[idx])+tox(kA))
    tw,tl=nf(T+beta*(-0) if False else T+beta+beta); assert tl==0,tl
    print('fibre target len',len(tw))
    Gr=Graph()
    for N in range(int(sys.argv[1])+1):
        for n in ([0] if N==0 else [N,-N]):
            c=beta*n if n>=0 else inv(beta)*(-n)
            fw,l=nf(c+kx+inv(c)); assert l==0
            Gr.add_loop(fw)
        print('N',N,'verts',len(Gr.e),'rank',Gr.rank(),'member',Gr.accepts(tw),flush=True)
