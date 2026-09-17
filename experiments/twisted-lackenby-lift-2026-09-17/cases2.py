from twisted_lift import *
T=[[0,1],[1,0]]; O=[[0,1],[1,1]]; I2=[[1,0],[0,1]]
# genus-2 surface <a,b,c,d | [a,b][c,d]>, rho(a)=T, rho(c)=O, b,d trivial -> image S3 on F_2^2
def comm(x,y): return [(x,1),(y,1),(x,-1),(y,-1)]
R=[comm(0,1)+comm(2,3)]
S=Setup(2,4,R,[T,I2,O,I2])
print("scalar H^1 basis", S.scalar_cocycles().tolist())
print("h^1(M)", len(S.derivations_mod_coboundaries()))
# sign character of Q=S3: a->1 (T odd), c->0 (O even), b,d->0
run_case("S2 h=2 all U", 2, 4, R, [T,I2,O,I2], Csel=[0,1])
run_case("S2 h=2 U=sign(a)", 2, 4, R, [T,I2,O,I2], Csel=[0,1], Uexplicit=[[1,0,0,0]])
run_case("S2 h=2 U=b", 2, 4, R, [T,I2,O,I2], Csel=[0,1], Uexplicit=[[0,1,0,0]])
run_case("S2 h=2 U=b,c,d", 2, 4, R, [T,I2,O,I2], Csel=[0,1], Uexplicit=[[0,1,0,0],[0,0,1,0],[0,0,0,1]])
run_case("S2 h=1 all U", 2, 4, R, [T,I2,O,I2], Csel=[0])
run_case("S2 h=3 all U", 2, 4, R, [T,I2,O,I2], Csel=[0,1,2])
