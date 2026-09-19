F := FreeGroup("a","b","c","d"); a:=F.1; b:=F.2; c:=F.3; d:=F.4;
G := F / [ b^a/b^3, c^b/c^3, d^c/d^3, a^d/a^3, Comm(a,c)^2, b^4, c^8 ];
gens := GeneratorsOfGroup(G);
for cl in [1..60] do
  hom := EpimorphismPGroup(G, 2, cl);
  P := Image(hom);
  Print("b^4=c^8=1: class ", cl, " actual ", PClassPGroup(P), " |P| = 2^", LogInt(Size(P),2), " ord(a,b,c,d) = ",
        List(gens, g -> Order(Image(hom, g))), "\n");
  if PClassPGroup(P) < cl then Print("2-quotient is finite\n"); break; fi;
od;
QUIT;
