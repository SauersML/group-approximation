# permsmall.g: small faithful permutation (= binary tree) model of a monolithic model file FILE.
# Q monolithic with socle <z>, z = a^(ord(a)/2): H is core-free iff z notin H.  Descend H := a random
# maximal subgroup of H while z lies in Frattini(H); then take a maximal subgroup avoiding z.
# (the descent is replaced by Grow below)  Keeps the best of TRIES random descents; writes OUT with permutations PA,PB,PC,PD and re-checks them.
Read(FILE); pc := Pcgs(MQ);; gi := List(MEXP, e -> PcElementByExponents(pc, e));;
z := gi[1]^(Order(gi[1])/2);; Reset(GlobalMersenneTwister, 1);; best := fail;;
RandMax := function(H, avoid)
  local hom, V, B, n, f, K;
  hom := NaturalHomomorphismByNormalSubgroup(H, FrattiniSubgroup(H)); V := Image(hom);
  B := Pcgs(V); n := Length(B);
  repeat
    f := Random(GF(2)^n);
    K := PreImage(hom, Subgroup(V, List(NullspaceMat(TransposedMat([f])), v -> Product([1..n], i -> B[i]^IntFFE(v[i])))));
  until IsZero(f) = false and (avoid = false or not z in K);
  return K;
end;;
# grow H from 1 inside its normalizer: add x from N(H) with x^2 in H and z notin <H,x>, as long as possible
Grow := function(H0)
  local H, N, cand, x, K, ok, i;
  H := H0;
  repeat
    ok := false; N := Normalizer(MQ, H);
    cand := Concatenation(Reversed(AsList(ModuloPcgs(N, H))), List([1..NR], i -> Random(N)));
    for x in cand do
      if x^2 in H and not x in H then
        K := ClosureGroup(H, x);
        if not z in K then H := K; ok := true; break; fi;
      fi;
    od;
  until not ok;
  return H;
end;;
for t in [1..TRIES] do
  H := Grow(TrivialSubgroup(MQ));
  if best = fail or Index(MQ, H) < Index(MQ, best) then best := H; Print("try ", t, " degree ", Index(MQ, H), "\n"); fi;
od;
act := FactorCosetAction(MQ, best);; pg := List(gi, g -> Image(act, g));;
F := FreeGroup("a","b","c","d");; rels := [ F.2^F.1/F.2^3, F.3^F.2/F.3^3, F.4^F.3/F.4^3, F.1^F.4/F.1^3, Comm(F.1,F.3)^2 ];;
Print("degree ", NrMovedPoints(pg), " ords ", List(pg, Order), " relators ", List(rels, r -> IsOne(MappedWord(r, GeneratorsOfGroup(F), pg))),
      " |image| = 2^", LogInt(Size(Group(pg)), 2), " cycle type of a ", CycleLengths(pg[1], [1..NrMovedPoints(pg)]){[1]}, "\n");
PrintTo(OUT, "# permutation model on ", NrMovedPoints(pg), " points\nPA := ", pg[1], ";\nPB := ", pg[2], ";\nPC := ", pg[3], ";\nPD := ", pg[4], ";\n");
QUIT;
