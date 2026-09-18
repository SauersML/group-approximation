"""Search for a window-[0,2] configuration of G_2 over GL_3(Z[1/2]):
M0, M1 in upper triangular GL_3(Z) (so <M0,M1> <= GL_3(Z)), M2 = diag(1,2,2),
[M1,M2] = 1, M2^-1 U M2 = U^2 with U = [M0,M1], U != 1, b1 != 1 and
V = M2 U M2^-1 non-integral (hence V not in <M0,M1>)."""
import itertools
from sympy import Matrix, diag, Rational
def cm(x,y): return x.inv()*y.inv()*x*y
M2 = diag(1,2,2); M2i = M2.inv()
I = Matrix.eye(3)
R = range(-1,2)
found = []
for d0 in itertools.product([1,-1],repeat=3):
  for (x12,x13,x23) in itertools.product(R,repeat=3):
    M0 = Matrix([[d0[0],x12,x13],[0,d0[1],x23],[0,0,d0[2]]])
    for d1 in itertools.product([1,-1],repeat=3):
      for w in R:
        M1 = Matrix([[d1[0],0,0],[0,d1[1],w],[0,0,d1[2]]])
        if cm(M1,M2) != I: continue
        U = cm(M0,M1)
        if U == I or M2i*U*M2 != U*U: continue
        b1 = cm(M0, M1*M0*M1.inv())
        if b1 == I: continue
        V = M2*U*M2i
        if all(v.is_integer for v in V): continue
        found.append((M0,M1,U,b1,V))
print(len(found), "configurations")
for M0,M1,U,b1,V in found[:3]:
    print("M0",M0.tolist(),"M1",M1.tolist(),"U",U.tolist(),"b1",b1.tolist(),"V",V.tolist())
