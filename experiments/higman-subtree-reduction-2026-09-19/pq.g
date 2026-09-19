F := FreeGroup("a","b","c","d"); a:=F.1; b:=F.2; c:=F.3; d:=F.4;
G := F / [ b^a/b^3, c^b/c^3, d^c/d^3, a^d/a^3, Comm(a,c)^2 ];
for cl in [1..40] do
  hom := EpimorphismPGroup(G, 2, cl);
  P := Image(hom);
  Print("class ", cl, " actual ", PClassPGroup(P), " |P| = 2^", LogInt(Size(P),2), " ord(a,b,c,d) = ",
        List(GeneratorsOfGroup(G), g -> Order(Image(hom, g))), "\n");
od;
QUIT;
