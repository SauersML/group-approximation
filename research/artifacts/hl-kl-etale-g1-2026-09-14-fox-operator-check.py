# Exact rational checks for etale-roots-lie-in-the-bicommutant-of-the-constants (lane hl-kl-etale-g1, 2026-09-14).
# Standard library only (fractions). Builds the Fox-derivative operator D_{T,c} from its definition
# (columns D(E_pq), coordinates E_11, E_12, ...) and prints roots, ranks and determinants.
from fractions import Fraction as Fr
def eye(n): return [[Fr(int(i==j)) for j in range(n)] for i in range(n)]
def mul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def inv(A):
    n=len(A); M=[row[:]+e for row,e in zip([r[:] for r in A],eye(n))]
    for c in range(n):
        p=next(r for r in range(c,n) if M[r][c]!=0); M[c],M[p]=M[p],M[c]
        pv=M[c][c]; M[c]=[x/pv for x in M[c]]
        for r in range(n):
            if r!=c and M[r][c]!=0:
                f=M[r][c]; M[r]=[x-f*y for x,y in zip(M[r],M[c])]
    return [row[n:] for row in M]
def rank(A):
    M=[r[:] for r in A]; rk=0; rows=len(M); cols=len(M[0])
    for c in range(cols):
        p=next((r for r in range(rk,rows) if M[r][c]!=0),None)
        if p is None: continue
        M[rk],M[p]=M[p],M[rk]
        for r in range(rows):
            if r!=rk and M[r][c]!=0:
                f=M[r][c]/M[rk][c]; M[r]=[x-f*y for x,y in zip(M[r],M[rk])]
        rk+=1
    return rk
def kron(A,B): return [[A[i//len(B)][j//len(B)]*B[i%len(B)][j%len(B)] for j in range(len(A)*len(B))] for i in range(len(A)*len(B))]
def letters(w,T,c):
    return [ (T if L=='x' else c[L]) if e==1 else inv(T if L=='x' else c[L]) for L,e in w]
def weval(w,T,c):
    M=eye(len(T))
    for X in letters(w,T,c): M=mul(M,X)
    return M
def Dmat(w,T,c):
    N=len(T); z=letters(w,T,c); l=len(w)
    S=[None]*(l+1); S[l]=eye(N)
    for i in range(l-1,-1,-1): S[i]=mul(z[i],S[i+1])
    cols=[]
    for p in range(N):
        for q in range(N):
            Y=[[Fr(int((i,j)==(p,q))) for j in range(N)] for i in range(N)]
            out=[[Fr(0)]*N for _ in range(N)]
            for i,(L,e) in enumerate(w):
                if L!='x': continue
                Si = S[i+1] if e==1 else S[i]   # letter index i is y_{i+1}: suffix after it is S[i+1]; for x^-1 use S_{i-1} = S[i]
                term=mul(mul(inv(Si),Y),Si)
                sg=1 if e==1 else -1
                out=[[o+sg*t for o,t in zip(ro,rt)] for ro,rt in zip(out,term)]
            cols.append([out[i][j] for i in range(N) for j in range(N)])
    return [[cols[j][i] for j in range(N*N)] for i in range(N*N)]
def det(A):
    M=[r[:] for r in A]; n=len(M); d=Fr(1)
    for c in range(n):
        p=next((r for r in range(c,n) if M[r][c]!=0),None)
        if p is None: return Fr(0)
        if p!=c: M[c],M[p]=M[p],M[c]; d=-d
        d*=M[c][c]
        for r in range(c+1,n):
            f=M[r][c]/M[c][c]; M[r]=[x-f*y for x,y in zip(M[r],M[c])]
    return d
w=[('x',1),('x',1),('a',1),('x',-1),('a',-1),('b',1)]
a=[[Fr(2),Fr(0)],[Fr(0),Fr(1)]]; one=eye(2); b=[[Fr(1),Fr(1)],[Fr(0),Fr(1)]]
print('semisimple tuple (diag(2,1),1):')
for t in [0,1,3,Fr(-2,7)]:
    T=[[Fr(1),Fr(t)],[Fr(0),Fr(1)]]
    print('  t=',t,' w=1:',weval(w,T,{'a':a,'b':one})==eye(2),' rank D =',rank(Dmat(w,T,{'a':a,'b':one})),'of 4')
T0=[[Fr(5,2),Fr(-4,3)],[Fr(9,2),Fr(-2)]]
print('node tuple (diag(2,1),1+E12): w(T0)=1:',weval(w,T0,{'a':a,'b':b})==eye(2),' det D(T0)=',det(Dmat(w,T0,{'a':a,'b':b})))
# amplification r=2: T0 (x) 1_2 root of amplified tuple, D rank
I2=eye(2); A2=kron(a,I2); B2=kron(b,I2); T02=kron(T0,I2)
print('amplified r=2: w=1:',weval(w,T02,{'a':A2,'b':B2})==eye(4),' rank D =',rank(Dmat(w,T02,{'a':A2,'b':B2})),'of 16')
T12=kron([[Fr(1),Fr(1)],[Fr(0),Fr(1)]],I2)
print('semisimple amplified r=2 at (1+E12)(x)1: rank D =',rank(Dmat(w,T12,{'a':A2,'b':eye(4)})),'of 16')
# sanity: D(1;1)= m id for w with trivial constants
print('sanity D_{1,1} = m id:',Dmat(w,eye(2),{'a':eye(2),'b':eye(2)})==[[Fr(int(i==j)) for j in range(4)] for i in range(4)])
print('--- D at node root T0 for (diag(2,1),1+E12); columns = D(E11),D(E12),D(E21),D(E22), entries in basis E11,E12,E21,E22')
M=Dmat(w,T0,{'a':a,'b':b})
for row in M: print('  ',[str(x) for x in row])
print('det =',det(M))
print('--- D at root 1+tE12 (t=1) for (diag(2,1),1)')
for row in Dmat(w,[[Fr(1),Fr(1)],[Fr(0),Fr(1)]],{'a':a,'b':one}): print('  ',[str(x) for x in row])
