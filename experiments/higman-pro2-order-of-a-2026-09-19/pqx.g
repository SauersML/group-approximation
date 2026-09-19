# usage: gap -q -c 'EXTRA:=[...];; NAME:="...";;' pqx.g
F := FreeGroup("a","b","c","d"); a:=F.1; b:=F.2; c:=F.3; d:=F.4;
rels := [ b^a/b^3, c^b/c^3, d^c/d^3, a^d/a^3, Comm(a,c)^2 ];
G := F / Concatenation(rels, EXTRA(a,b,c,d));
gens := GeneratorsOfGroup(G); t0 := Runtime();
for cl in [1..60] do
  hom := EpimorphismPGroup(G, 2, cl); P := Image(hom);
  Print(NAME, " class ", cl, " actual ", PClassPGroup(P), " |P| = 2^", LogInt(Size(P),2),
        " ords ", List(gens, g -> Order(Image(hom, g))), " s ", Int((Runtime()-t0)/1000), "\n");
  if PClassPGroup(P) < cl then Print(NAME, " finite\n"); break; fi;
od;
QUIT;
