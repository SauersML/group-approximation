# Induced-representation test for R=[a,c]^2 over K1 = <a,b,c> in Gamma(3,m), m=2^e.
# The j-th wreath coordinate of [a,c] (transversal b^j of A in K1) is a^-1 c^-u a c^v with
# u = 3^(j*3^-1 mod m), v = 3^j (exponents mod m).  K1 -> Abar wr Sym(m) kills R iff every
# coordinate squared is trivial in Abar = <a,c | a^m, c^m, [a,c]^2>.  We test nontriviality of the
# coordinates in 2-quotients of Abar (a nontrivial image proves the coordinate is not in <<R>>).
F:=FreeGroup("a","c");; a:=F.1;; c:=F.2;;
for e in [2,3,4] do
  m:=2^e;; ninv:=Inverse(3) mod m;;
  G:=F/[a^m,c^m,Comm(a,c)^2];;
  P:=EpimorphismPGroup(G,2,8);;
  for j in [0..m-1] do
    u:=PowerMod(3,(j*ninv) mod m,m);; v:=PowerMod(3,j,m);;
    w:=(a^-1*c^-u*a*c^v)^2;;
    Print("m=",m," j=",j," u=",u," v=",v," order of coordinate^2 in class-8 2-quotient: ",
      Order(Image(P,MappedWord(w,[a,c],GeneratorsOfGroup(G)))),"\n");
  od;
od;
QUIT;
