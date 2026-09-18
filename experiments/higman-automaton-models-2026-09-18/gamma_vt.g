# Gamma_e = H4(3)/<<a^q,b^q,c^q,d^q>>, q = 2^e.  In the class-e lower exponent-2 central quotient P:
# do the four vertex groups <a,b>,<b,c>,<c,d>,<d,a> (order q^2 in Gamma_e) inject?  If they do, the
# kernel is a torsion-free normal subgroup of finite index (every finite subgroup of Gamma_e fixes a
# point of the CAT(0) square complex, so is conjugate into a vertex group).
# Second part: the same for Gamma_e / <<[a,c]^2>>: orders of the generators and of <a,c>.
F:=FreeGroup("a","b","c","d");; a:=F.1;;b:=F.2;;c:=F.3;;d:=F.4;;
n:=3;; rels:=[b^a*b^-n, c^b*c^-n, d^c*d^-n, a^d*a^-n];;
for e in [2,3,4,5] do
  q:=2^e;
  G:=F/Concatenation(rels,[a^q,b^q,c^q,d^q]);;
  P:=EpimorphismPGroup(G,2,e);; g:=List(GeneratorsOfGroup(G),x->Image(P,x));;
  Print("Gamma_",e," class ",e," log2|P|=",Log(Size(Image(P)),2)," log2|vertex groups|=",
    List([1..4],i->Log(Size(Group(g[i],g[1+(i mod 4)])),2)),"  (2e=",2*e,")\n");
od;
for e in [2,3,4,5] do
  q:=2^e;
  G:=F/Concatenation(rels,[a^q,b^q,c^q,d^q,Comm(a,c)^2]);;
  for K in [e..e+3] do
    P:=EpimorphismPGroup(G,2,K);; g:=List(GeneratorsOfGroup(G),x->Image(P,x));;
    Print("Gamma_",e,"/[a,c]^2 class ",K," log2|P|=",Log(Size(Image(P)),2)," log2ord=",
      List(g,x->Log(Order(x),2))," log2|<a,c>|=",Log(Size(Group(g[1],g[3])),2),
      " log2|<a,b>|=",Log(Size(Group(g[1],g[2])),2),"\n");
  od;
od;
QUIT;
