EVALS:=[3,4,5,6,7];
# Discreteness criterion for Gamma(3,2^e) acting on T_B (see higman-b-splitting README).
# rho_v : B -> Sym(S_2(v)); rho_w(b)=rho_v(d), rho_w(d)=rho_v(b) (sigma^2 swaps the ends of the base edge).
# If |rho_v(B)| = |<(rho_v b, rho_v d),(rho_v d, rho_v b)>| then ker rho_v is sigma^2-invariant, so
# Fix(B(v,2)) = Fix(B(v,3)) at both vertex types, hence Fix(B(v,2)) = Lambda_B (kernel on T_B) and
# L1/Lambda_B = image of L1 on S_2(v) is finite.
for e in EVALS do
  Read(Concatenation("ball_e",String(e),"_r2.g"));
  n:=LargestMovedPoint([pa,pb,pd]);; sh:=MappingPermListList([1..n],[n+1..2*n]);;
  GB:=Group(pb,pd);; sB:=Size(GB);;
  pb2:=pb*pd^sh;; pd2:=pd*pb^sh;; sB2:=Size(Group(pb2,pd2));;
  sL:=Size(Group(pa,pb,pd));;
  Print("e=",e," log2|L1bar|=",Log(sL,2)," log2|Bbar|=",Log(sB,2)," log2|Bbar diag|=",Log(sB2,2),
        " discrete=",sB=sB2," Bbar abelian=",IsAbelian(GB)," ord b,d in Bbar=",[Order(pb),Order(pd)],"\n");
od;
QUIT;
