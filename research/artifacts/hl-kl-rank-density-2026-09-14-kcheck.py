# Exact check of the commutant construction in Theorem K on a small instance.
from fractions import Fraction as Fr
import random
random.seed(7)
def mat(n,m,f): return [[f(i,j) for j in range(m)] for i in range(n)]
def mul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def add(A,B): return [[A[i][j]+B[i][j] for j in range(len(A[0]))] for i in range(len(A))]
def kron(A,B): return [[A[i//len(B)][j//len(B[0])]*B[i%len(B)][j%len(B[0])] for j in range(len(A[0])*len(B[0]))] for i in range(len(A)*len(B))]
n,r=2,6; N=n*r
I_r=mat(r,r,lambda i,j:Fr(int(i==j)))
a=[[Fr(2),Fr(1)],[Fr(1),Fr(1)]]; b=[[Fr(1),Fr(1)],[Fr(0),Fr(1)]]
A=kron(a,I_r); B=kron(b,I_r)
# rank-one perturbation E = p q^T supported inside C^n (x) span(e_0), so S2 = span(e_0), S1 = {s : C^n(x)s in ker E}
p=[Fr(random.randint(-3,3)) for _ in range(N)]
q=[Fr(0)]*N
for i in range(n): q[i*r+1]=Fr(random.randint(1,4))   # q supported on C^n (x) e_1, so ker E contains C^n (x) s for s with s_1 = 0
p=[Fr(0)]*N
for i in range(n): p[i*r+0]=Fr(random.randint(1,4))   # range E inside C^n (x) e_0
E=[[p[i]*q[j] for j in range(N)] for i in range(N)]
Bp=add(B,E)
# u in S1 (u_1 = 0), v in S2^perp (v_0 = 0), nonzero v^T u irrelevant
u=[Fr(0)]*r; u[3]=Fr(1); u[5]=Fr(2)
v=[Fr(0)]*r; v[2]=Fr(1); v[4]=Fr(-1)
Y=[[u[i]*v[j] for j in range(r)] for i in range(r)]
X=kron(mat(n,n,lambda i,j:Fr(int(i==j))),Y)
ok=lambda M1,M2: M1==M2
print('X commutes with A:', ok(mul(X,A),mul(A,X)))
print('X commutes with B+E:', ok(mul(X,Bp),mul(Bp,X)))
print('E rank-one nonzero:', any(x!=0 for row in E for x in row))
print('X does NOT commute with E if u violates S1 (control):')
u2=[Fr(0)]*r; u2[1]=Fr(1); Y2=[[u2[i]*v[j] for j in range(r)] for i in range(r)]; X2=kron(mat(n,n,lambda i,j:Fr(int(i==j))),Y2)
print('  control commutes with B+E:', ok(mul(X2,Bp),mul(Bp,X2)))
