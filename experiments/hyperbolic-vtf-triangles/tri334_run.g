Read("tri334_lib.g");
V := Filtered(Elements(GF(2)^3), v -> not IsZero(v));
X1 := Action(SL(3,2), V, OnRight);                       # L3(2) on the 7 points; X2 is a second copy
k := Position(V, V[1] + V[2]);
P1 := Stabilizer(X1, 1); L1 := Stabilizer(X1, Set([1, 2, k]), OnSets); B1 := Intersection(P1, L1);
X0 := AlternatingGroup(6);
P0 := Stabilizer(X0, [1,2], OnSets);
L0 := Stabilizer(X0, Set([Set([1,2]), Set([3,4]), Set([5,6])]), OnSetsSets);
B0 := Intersection(P0, L0);
Print("links: X1 ", CosetGraphGirthFace(X1, P1, L1), "  X0 ", CosetGraphGirthFace(X0, P0, L0), "\n");

Gen2 := function(E) local s; s := SmallGeneratingSet(E); if Length(s) <> 2 then Error("not 2-generated"); fi; return s; end;
y0 := First(AsList(X1), g -> Order(g) = 7);

# Pattern [a,b,c]: X0 uses [P0,L0][a] for edge 01; X1 uses [P1,L1][b] for edge 01; X2 uses [P1,L1][c] for edge 02.
MakePattern := function(a, b, c)
  local R, E001, E002, E101, E112, E202, E212, I01, I02, I12, triples, h01, h02, h12, g1, g2, hom1, hom2;
  E001 := [P0, L0][a]; E002 := [P0, L0][3 - a];
  E101 := [P1, L1][b]; E112 := [P1, L1][3 - b];
  E202 := [P1, L1][c]; E212 := [P1, L1][3 - c];
  I01 := IsosMappingFace(E001, E101, B0, B1);
  I02 := IsosMappingFace(E002, E202, B0, B1);
  I12 := IsosMappingFace(E112, E212, B1, B1);
  triples := [];
  for h01 in I01 do for h02 in I02 do for h12 in I12 do
    if ForAll(GeneratorsOfGroup(B0), x -> Image(h12, Image(h01, x)) = Image(h02, x)) then
      Add(triples, [Position(I01, h01), Position(I02, h02), h12]);
    fi;
  od; od; od;
  g1 := Gen2(E101); g2 := Gen2(E202);
  hom1 := IsomorphismFpGroupByGenerators(X1, [g1[1], g1[2], y0]);
  hom2 := IsomorphismFpGroupByGenerators(X1, [g2[1], g2[2], y0]);
  return rec(pat := [a,b,c], I01 := I01, I02 := I02, triples := triples, g1 := g1, g2 := g2,
             hom1 := hom1, hom2 := hom2, E112 := E112);
end;

CompletionSearch := function(F, R)
  local cl7, monos, auts, phi, a, phi0, found, byIso01, byIso02, t, i, j, h12, y1, y2, im1, im2, s1, s2, fg1, fg2, rel1, rel2, cgens;
  cl7 := Filtered(ConjugacyClasses(F), c -> Order(Representative(c)) = 7);
  monos := IsomorphicSubgroups(F, X0);
  auts := AutomorphismGroup(X0);
  auts := List(RightTransversal(auts, InnerAutomorphismsAutomorphismGroup(auts)), x -> x);
  fg1 := FreeGeneratorsOfFpGroup(Range(R.hom1)); rel1 := RelatorsOfFpGroup(Range(R.hom1));
  fg2 := FreeGeneratorsOfFpGroup(Range(R.hom2)); rel2 := RelatorsOfFpGroup(Range(R.hom2));
  cgens := GeneratorsOfGroup(R.E112);
  found := List(R.triples, t -> 0);
  for phi in monos do for a in auts do
    phi0 := a * phi;
    s1 := List(R.I01, h -> List(R.g1, g -> Image(phi0, PreImagesRepresentative(h, g))));
    s2 := List(R.I02, h -> List(R.g2, g -> Image(phi0, PreImagesRepresentative(h, g))));
    byIso01 := List(s1, s -> ExtendByScan(F, rel1, fg1, s[1], s[2], cl7, 168));
    byIso02 := List(s2, s -> ExtendByScan(F, rel2, fg2, s[1], s[2], cl7, 168));
    for t in [1..Length(R.triples)] do
      i := R.triples[t][1]; j := R.triples[t][2]; h12 := R.triples[t][3];
      for y1 in byIso01[i] do for y2 in byIso02[j] do
        im1 := [s1[i][1], s1[i][2], y1]; im2 := [s2[j][1], s2[j][2], y2];
        if ForAll(cgens, c -> MappedWord(UnderlyingElement(Image(R.hom1, c)), fg1, im1)
                            = MappedWord(UnderlyingElement(Image(R.hom2, Image(h12, c))), fg2, im2)) then
          found[t] := found[t] + 1;
        fi;
      od; od;
    od;
  od; od;
  return found;
end;

for a in [1,2] do for b in [1,2] do for c in [1,2] do
  R := MakePattern(a, b, c);
  Print("pattern ", R.pat, ": #isos ", [Length(R.I01), Length(R.I02)], " #consistent triples ", Length(R.triples), "\n");
  if Length(R.triples) > 0 then
    for F in [AlternatingGroup(7), AlternatingGroup(8), AlternatingGroup(9)] do
      t0 := Runtime();
      res := CompletionSearch(F, R);
      Print("   |F|=", Size(F), " triples with a completion: ", Number(res, x -> x > 0), "/", Length(res),
            " hits ", res, " ms=", Runtime() - t0, "\n");
    od;
  fi;
od; od; od;
Print("DONE\n");
QUIT;
