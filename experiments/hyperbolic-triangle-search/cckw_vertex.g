# cckw_vertex.g -- vertex groups of the 19 CCKW (6,6,8) trivalent triangle groups with no non-abelian
# simple quotient found by CCKW (source table_3_3_4.tex: empty L_2-quotients and small quotients,
# alternating degrees in {3,4}). For each vertex X = <x,y | vertex relators> of the core report |X|,
# structure, girth of Gamma(X;<x>,<y>), and the faithful irreducible characters of degree <= 6 with the
# eigenvalue multiplicities of x and y (for eigenvalues 1, E(3), E(3)^2). Requires cckw334.g from
# cckw_convert.py (words in a, b, c).
Read("girth_lib.g");
F := FreeGroup("a", "b", "c"); a := F.1; b := F.2; c := F.3;
Read("cckw334.g");
Letters := w -> Set(List(LetterRepAssocWord(w), AbsInt));
EigMult := function(chi, g, X)
  local cls, pos;
  cls := ConjugacyClasses(X);
  pos := j -> PositionProperty(cls, cl -> g^j in cl);
  return List([0..2], k -> Sum([0..2], j -> chi[pos(j)] * E(3)^(-k*j)) / 3);
end;
VertexData := function(rels, i, j)
  local FF, rr, G0, iso, X, x, y, chis;
  FF := FreeGroup("x", "y");
  rr := Filtered(rels, w -> IsSubset([i, j], Letters(w)));
  rr := List(rr, w -> MappedWord(w, GeneratorsOfGroup(F){[i, j]}, GeneratorsOfGroup(FF)));
  G0 := FF / rr;
  iso := IsomorphismPermGroup(G0); X := Image(iso);
  x := Image(iso, G0.1); y := Image(iso, G0.2);
  chis := Filtered(Irr(X), chi -> chi[1] <= 6 and Size(KernelOfCharacter(chi)) = 1);
  return rec(order := Size(X), struct := StructureDescription(X),
             girth := CosetGraphGirth(X, Group(x), Group(y)),
             faithful := List(chis, chi -> [chi[1], EigMult(chi, x, X), EigMult(chi, y, X)]));
end;
for G in CCKW do
  Print(G.name, "\n");
  for pr in [[1, 2], [2, 3], [3, 1]] do
    D := VertexData(G.rels, pr[1], pr[2]);
    Print("  vertex ", "abc"{pr}, ": |X|=", D.order, " ", D.struct, " girth=", D.girth,
          " faithful irreps deg<=6 [deg, eig(x), eig(y)]: ", D.faithful, "\n");
  od;
od;
Print("CCKW_VERTEX_DONE\n");
QUIT;
