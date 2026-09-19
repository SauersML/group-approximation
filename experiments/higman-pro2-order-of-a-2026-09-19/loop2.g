# class loop of grow2.g (resumable from a saved workspace)
while cl < MAXCL do
  if DefineNewGenerators(qs) = fail then Print(NAME, " collector too small\n"); break; fi;
  ComputeTails(qs); EvaluateConsistency(qs); LiftEpimorphism(qs);
  n := GeneratorNumberOfQuotient(qs); c := qs!.numberOfHighestWeightGenerators;
  M := CentralRelations(qs);
  R := List(M.bound, i -> M.matrix[i] * One(GF(2)));
  r0 := Length(R);
  tails := List([1..4], i -> TailOfPower(qs, i, ords[i]));
  keep := []; basis := ShallowCopy(R); dbl := [];
  for i in PRIO do
    if RankMat(Concatenation(basis, [tails[i]])) > Length(basis) then
      Add(basis, tails[i]); Add(keep, tails[i]);
    fi;
  od;
  for i in [1..4] do
    if Length(R) = 0 or RankMat(Concatenation(R, [tails[i]])) > Length(R) then Add(dbl, i); fi;
  od;
  q := c - r0;
  if q > KEEP then
    while Length(keep) < KEEP do
      v := Random(GF(2)^c);
      if RankMat(Concatenation(basis, [v])) > Length(basis) then Add(basis, v); Add(keep, v); fi;
    od;
    compl := BaseSteinitzVectors(IdentityMat(c, GF(2)), basis).factorspace;
    for v in compl do AddVectorLTM(M, v); od;
  fi;
  for i in dbl do ords[i] := 2*ords[i]; od;
  IncorporateCentralRelations(qs);
  if qs!.numberOfHighestWeightGenerators > Length(qs!.eliminatedGens) then
    RenumberHighestWeightGenerators(qs);
  else
    Print(NAME, " finite: no new layer at class ", cl+1, "\n"); break;
  fi;
  cl := cl + 1;
  if IsBound(CKPT) and CKPT then SaveWorkspace(Concatenation(NAME, ".ws")); fi;
  Print(NAME, " class ", cl, " layer ", Minimum(q, KEEP), "/", q, " |P| = 2^", GeneratorNumberOfQuotient(qs),
        " ords ", ords, " s ", Int((Runtime()-t0)/1000), "\n");
od;
# independent re-check in the resulting pc group
P := GroupByQuotientSystem(qs);
hom := EpimorphismQuotientSystem(qs);
gi := List(GeneratorsOfGroup(G), g -> Image(hom, g));
ok := ForAll(rels, r -> IsOne(MappedWord(r, GeneratorsOfGroup(F), gi)));
Print(NAME, " FINAL class ", cl, " |P| = 2^", LogInt(Size(P), 2), " relators hold: ", ok,
      " ords recomputed ", List(gi, Order), " generate: ", Size(Group(gi)) = Size(P), "\n");
QUIT;
