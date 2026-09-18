# Gamma_e = H4(3)/<<a^q,b^q,c^q,d^q>>, q=2^e.  Lower exponent-2 central quotients by class:
# does the full order q of the generators survive in a finite 2-quotient?
F:=FreeGroup("a","b","c","d");; a:=F.1;;b:=F.2;;c:=F.3;;d:=F.4;;
n:=3;; rels:=[b^a*b^-n, c^b*c^-n, d^c*d^-n, a^d*a^-n];;
for e in [2,3,4,5] do
  q:=2^e;
  G:=F/Concatenation(rels,[a^q,b^q,c^q,d^q]);;
  gens:=GeneratorsOfGroup(G);;
  for K in [e..e+2] do
    P:=EpimorphismPGroup(G,2,K);; I:=Image(P);;
    Print("e=",e," class<=",K," log2|G|=",Log(Size(I),2),
       " log2ord=",List(gens,x->Log(Order(Image(P,x)),2)),"\n");
  od;
od;
QUIT;
