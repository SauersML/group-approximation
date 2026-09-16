# Referee check (2026-09-16): Lemma 6 of the Sol calibration with a SYMBOLIC base point p0=(x,y).
# Prints sh(P_{w_n}) - det(M^n e1, M^-n e1) as a polynomial in x,y; all zeros means base-point-independent identity.
import sympy as sp
x,y=sp.symbols('x y')
def check(M,n):
    M=sp.Matrix(M); Mi=M.inv()
    word='t'*n+'a'+'T'*n + 'T'*n+'a'+'t'*n
    inv={'t':'T','T':'t','a':'A','A':'a'}
    A1='t'*n+'a'+'T'*n; B1='T'*n+'a'+'t'*n
    word=A1+B1+''.join(inv[c] for c in reversed(A1))+''.join(inv[c] for c in reversed(B1))
    L=sp.eye(2); c=sp.Matrix([0,0]); p0=sp.Matrix([x,y])
    pts=[p0]
    gen={'t':(M,sp.Matrix([0,0])),'T':(Mi,sp.Matrix([0,0])),'a':(sp.eye(2),sp.Matrix([1,0])),'A':(sp.eye(2),sp.Matrix([-1,0]))}
    for ch in word:
        Ls,cs=gen[ch]; c=c+L*cs; L=L*Ls; pts.append(L*p0+c)
    assert pts[-1]==p0
    sh=sum(sp.Matrix.hstack(pts[i],pts[i+1]).det() for i in range(len(pts)-1))/2
    u=M**n*sp.Matrix([1,0]); v=M**(-n)*sp.Matrix([1,0])
    return sp.expand(sh - sp.Matrix.hstack(u,v).det())
for M in [[[2,1],[1,1]],[[0,1],[1,1]],[[5,3],[3,2]],[[4,-1],[1,0]],[[1,2],[1,1]], [[-3,1],[-1,0]]]:
    print(M,[check(M,n) for n in range(1,6)], sp.Matrix(M).det())
