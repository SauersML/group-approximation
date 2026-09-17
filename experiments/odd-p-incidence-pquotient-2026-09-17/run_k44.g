OnBreak := function() FORCE_QUIT_GAP(3); end;
Read("pq.g"); Read("graphs.g");
G := SolGroup(8, k44, 3, [1]); ne := G[2]; G := G[1];
for c in [5..7] do
  t := Runtime();
  hom := EpimorphismPGroup(G, 3, c);
  Print("K44 p=3 class<=", c, " |P|=3^", Length(Factors(Size(Image(hom)))), " J nontrivial: ", not IsOne(Image(hom, GeneratorsOfGroup(G)[ne+1])), " (", Runtime()-t, "ms)\n");
od;
QUIT;
