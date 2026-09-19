"""Independent exact check of the H_4 (and A_4, B_4) VC-failure tuple in a Burau-type linear representation of the
Artin group over Q(sqrt5) at t = 2: s_i e_i = -t e_i, s_i e_j = e_j + a_ij e_i, with a_ij = 0 if m_ij = 2, and
a_ij = 1, a_ji = t(2 + 2cos(2 pi/m)) for i < j adjacent.  The braid relations are verified exactly first, so this is a
representation; distinct images then certify distinct group elements (equal images certify nothing)."""
import sys
from fractions import Fraction as Fr
class Q5:
    def __init__(s,p,q=0): s.p=Fr(p); s.q=Fr(q)
    def __add__(s,o): o=o if isinstance(o,Q5) else Q5(o); return Q5(s.p+o.p,s.q+o.q)
    def __sub__(s,o): o=o if isinstance(o,Q5) else Q5(o); return Q5(s.p-o.p,s.q-o.q)
    def __mul__(s,o): o=o if isinstance(o,Q5) else Q5(o); return Q5(s.p*o.p+5*s.q*o.q,s.p*o.q+s.q*o.p)
    def __neg__(s): return Q5(-s.p,-s.q)
    def inv(s): d=s.p*s.p-5*s.q*s.q; return Q5(s.p/d,-s.q/d)
    def __eq__(s,o): o=o if isinstance(o,Q5) else Q5(o); return s.p==o.p and s.q==o.q
Z,O=Q5(0),Q5(1)
def mm(A,B): return [[sum((A[i][k]*B[k][j] for k in range(4)),Z) for j in range(4)] for i in range(4)]
def minv(A):
    n=4; M=[row[:]+[O if i==j else Z for j in range(n)] for i,row in enumerate(A)]
    for c in range(n):
        p=next(r for r in range(c,n) if not M[r][c]==Z); M[c],M[p]=M[p],M[c]
        iv=M[c][c].inv(); M[c]=[x*iv for x in M[c]]
        for r in range(n):
            if r!=c and not M[r][c]==Z:
                f=M[r][c]; M[r]=[x-f*y for x,y in zip(M[r],M[c])]
    return [row[n:] for row in M]
CM={3:Q5(1),4:Q5(2),5:Q5(Fr(3,2),Fr(1,2)),6:Q5(3)}
def rep(md,t=Q5(2)):
    m=lambda i,j: md.get((min(i,j),max(i,j)),2)
    S=[]
    for i in range(4):
        A=[[O if r==c else Z for c in range(4)] for r in range(4)]   # columns = images of e_c
        A[i][i]=-t
        for j in range(4):
            if j!=i and m(i,j)>2: A[i][j]=O if i<j else t*CM[m(i,j)]
        S.append(A)
    return S,[minv(A) for A in S],m
def img(S,Si,w):
    M=[[O if r==c else Z for c in range(4)] for r in range(4)]
    for l in w: M=mm(M,S[l-1] if l>0 else Si[-l-1])
    return M
MD={'H4':{(0,1):3,(1,2):3,(2,3):5},'A4':{(0,1):3,(1,2):3,(2,3):3},'B4':{(0,1):3,(1,2):3,(2,3):4}}
def inv(w): return [-g for g in reversed(w)]
def com(x,y): return x+y+inv(x)+inv(y)
for name in sys.argv[1:] or ['H4']:
    S,Si,m=rep(MD[name])
    ok=True
    for i in range(4):
        for j in range(i+1,4):
            k=m(i,j); x=[(i+1) if r%2==0 else (j+1) for r in range(k)]; y=[(j+1) if r%2==0 else (i+1) for r in range(k)]
            ok&= img(S,Si,x)==img(S,Si,y)
    E=lambda w: img(S,Si,w)
    P3,P2,P1=[1,1],[1,2,2,-1],[1,2,3,3,-2,-1]
    a=P2+P3; b=P1+P3; c=[4,4]; d=[-3,4,4,3]; w=[2,3,4,4,-3,-2]; u=w+c; v=w+d; k=com(u,a); I=E([])
    print(name,'braid relations hold:',ok)
    print('  equalities (consistency): [c,a]=1',E(com(c,a))==I,'[d,b]=1',E(com(d,b))==I,'[u,a]=[v,b]',E(k)==E(com(v,b)))
    print('  certified inequalities: k!=1',not E(k)==I,'[u,b]!=k',not E(com(u,b))==E(k),'[v,a]!=k',not E(com(v,a))==E(k),
          '[c,b]!=1',not E(com(c,b))==I,'[d,a]!=1',not E(com(d,a))==I)
