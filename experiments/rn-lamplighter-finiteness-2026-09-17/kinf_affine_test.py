# K_infinity membership test for relators of the affine self-similar group Z[1/m] x <u> acting on Z_p.
# Generators t = x+1 and a = u*x; S = their section closure (pairs (u,b) for x -> u x + b).
# Words are tuples of letters (index into S, +-1), acting right to left.
# inK(w): graph of freely reduced iterated sections of w.
#   'notN'     : some vertex permutes the first level (w not in N);
#   ('cyc',n)  : the graph (n vertices) has a directed cycle, so w is NOT in K_infinity;
#   ('K',n)    : the graph is finite and acyclic, so w IS in K_infinity.
# Tested: the BS relator a t^den a^-1 t^-num and r_k = [t, a^k t a^-k], k = 1..K.
# Usage: nice -n 19 python3 kinf_affine_test.py p u K     (e.g. 5 2/3 4)
from fractions import Fraction as Fr
import sys
sys.setrecursionlimit(100000)
p=int(sys.argv[1]); u=Fr(sys.argv[2])
def modp(q): return (q.numerator*pow(q.denominator,-1,p))%p
def act(g,d):
    uu,c=g; v=uu*d+c; dd=modp(v); return dd,(uu,(v-dd)/p)
gens=[(Fr(1),Fr(1)),(u,Fr(0))]
S=set(gens); todo=list(gens)
while todo:
    g=todo.pop()
    for d in range(p):
        _,h=act(g,d)
        if h not in S: S.add(h); todo.append(h)
S.discard((Fr(1),Fr(0))); S=sorted(S); idx={g:i for i,g in enumerate(S)}
def inv(g): uu,c=g; return (1/uu,-c/uu)
def letter_act(l,d):  # l=(i,e)
    i,e=l; g=S[i]
    if e==1:
        dd,h=act(g,d); return dd,h
    gi=inv(g)  # find d0 with g(d0)=d
    for d0 in range(p):
        if act(g,d0)[0]==d: break
    _,h=act(g,d0); return d0,('inv',h)
def tolet(h):
    if h[0]=='inv':
        h=h[1]; 
        return None if h==(1,0) else (idx[h],-1)
    return None if h==(1,0) else (idx[h],1)
def reduce(w):
    out=[]
    for l in w:
        if out and out[-1][0]==l[0] and out[-1][1]==-l[1]: out.pop()
        else: out.append(l)
    return tuple(out)
def sections(w):  # returns perm and list of section words
    res=[]; perm=[]
    for d in range(p):
        x=d; sec=[]
        for l in reversed(w):
            x,h=letter_act(l,x); L=tolet(h)
            if L: sec.append(L)
        perm.append(x); res.append(reduce(tuple(reversed(sec))))
    return perm,res
def inK(w, cap=200000):
    w=reduce(w); seen={}; 
    stack=[w]; graph={}
    while stack:
        x=stack.pop()
        if x in graph or not x: continue
        pm,ss=sections(x)
        if pm!=list(range(p)): return 'notN'
        graph[x]=[s for s in ss if s]
        if len(graph)>cap: return 'cap'
        stack.extend(graph[x])
    # acyclic?
    color={}
    def dfs(v):
        color[v]=1
        for y in graph[v]:
            if color.get(y)==1: return False
            if y not in color and not dfs(y): return False
        color[v]=2; return True
    for v in graph:
        if v not in color and not dfs(v): return ('cyc',len(graph))
    return ('K',len(graph))
T=(idx[(Fr(1),Fr(1))],1); A=(idx[(u,Fr(0))],1)
def I(w): return tuple((i,-e) for i,e in reversed(w))
print('S=',S)
num,den=u.numerator,u.denominator
bs=(A,)+(T,)*den+I((A,))+ I((T,)*num)
print('BS', inK(bs))
for k in range(1,int(sys.argv[3])+1):
    ak=(A,)*k; conj=ak+(T,)+I(ak)
    r=(T,)+conj+I((T,))+I(conj)
    print(k, inK(r))
