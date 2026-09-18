# The b-twist of R = [a,c]^2 over K1 = <a,b,c> in Gamma(3,m), m = 2^e.
# Identity (proof, section 1): in K1, b^-1 [a,c] b = a^-1 c^-lam a c^3 with t = 3^-1 mod m and
# lam = 3^t mod m.  So S_e := b^-1 R b = (a^-1 c^-lam a c^3)^2 lies in A and in <<R>>_K1.
# Part 1 (sanity only): the identity holds in finite 2-quotients of K1.
# Part 2 (certificate): S_e is NONTRIVIAL in a finite 2-quotient of Abar_m = <a,c | a^m, c^m, R>,
#   hence S_e is not in <<R>>_A: the Freiheitssatz A/<<R>>_A -> K1/<<R>>_K1 fails.
#   Since lam = 3 mod 8 for every e >= 3, the image of S_e in Abar_8 is [a,c^3]^2, so the single
#   e = 3 certificate covers every e >= 3.
# Part 3: abelian invariants of the image of <a,c> in 2-quotients of Gamma(3,2^e)/<<R>>.
F:=FreeGroup("a","b","c");; a:=F.1;; b:=F.2;; c:=F.3;;
lamof:=function(m) local t; t:=Inverse(3) mod m; return PowerMod(3,t,m); end;;
Print("Part 1: identity b^-1[a,c]b = a^-1 c^-lam a c^3 in 2-quotients of K1(m)\n");
for e in [2..5] do
  m:=2^e;; lam:=lamof(m);;
  G:=F/[a^m,b^m,c^m,b^a*b^-3,c^b*c^-3];;
  P:=EpimorphismPGroup(G,2,e+2);;
  w:=b^-1*Comm(a,c)*b*(a^-1*c^-lam*a*c^3)^-1;;
  Print("  e=",e," lam=",lam," class ",e+2," log2|P|=",Log(Size(Image(P)),2),
    " image of identity defect trivial: ",
    IsOne(Image(P,MappedWord(w,[a,b,c],GeneratorsOfGroup(G)))),"\n");
od;
Print("Part 2: S_e = (a^-1 c^-lam a c^3)^2 in 2-quotients of Abar_m\n");
F2:=FreeGroup("a","c");; x:=F2.1;; y:=F2.2;;
for e in [3..6] do
  m:=2^e;; lam:=lamof(m);;
  G:=F2/[x^m,y^m,Comm(x,y)^2];;
  for K in [4..7] do
    P:=EpimorphismPGroup(G,2,K);;
    S:=(x^-1*y^-lam*x*y^3)^2;;
    Print("  e=",e," lam=",lam," lam mod 8=",lam mod 8," class ",K," log2|P|=",
      Log(Size(Image(P)),2)," order of image of S_e: ",
      Order(Image(P,MappedWord(S,[x,y],GeneratorsOfGroup(G)))),"\n");
  od;
od;
Print("Part 3: <a,c> in 2-quotients of Gamma(3,2^e)/<<[a,c]^2>>\n");
F4:=FreeGroup("a","b","c","d");; A:=F4.1;; B:=F4.2;; C:=F4.3;; D:=F4.4;;
rels:=[B^A*B^-3, C^B*C^-3, D^C*D^-3, A^D*A^-3];;
for e in [4,5] do
  m:=2^e;;
  G:=F4/Concatenation(rels,[A^m,B^m,C^m,D^m,Comm(A,C)^2]);;
  for K in [e+1..e+2] do
    P:=EpimorphismPGroup(G,2,K);; g:=List(GeneratorsOfGroup(G),z->Image(P,z));;
    H:=Group(g[1],g[3]);;
    Print("  e=",e," class ",K," log2ord=",List(g,z->Log(Order(z),2)),
      " AbelianInvariants(<a,c>)=",AbelianInvariants(H),
      " c^16 in <a,c>': ",g[3]^16 in DerivedSubgroup(H),"\n");
  od;
od;
QUIT;
