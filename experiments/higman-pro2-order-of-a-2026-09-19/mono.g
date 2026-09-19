# Monolithic reduction: from the class-CL 2-quotient P of G/<<EXTRA>> pass to P/N with N maximal normal
# not containing z = a^(ord(a)/2); P/N then has socle <z>.  Each step kills a complement of <z> in
# Omega_1(Z(Q)).  The result is a (much smaller) finite 2-quotient of G with the same ord(a).
F := FreeGroup("a","b","c","d"); a:=F.1; b:=F.2; c:=F.3; d:=F.4;
rels := Concatenation([ b^a/b^3, c^b/c^3, d^c/d^3, a^d/a^3, Comm(a,c)^2 ], EXTRA(a,b,c,d));
G := F / rels;
hom := EpimorphismPGroup(G, 2, CL); Q := Image(hom);
gi := List(GeneratorsOfGroup(G), g -> Image(hom, g));
Print(NAME, " start |Q| = 2^", LogInt(Size(Q),2), " ords ", List(gi, Order), "\n");
t0 := Runtime();
repeat
  z := gi[1]^(Order(gi[1])/2);
  ZQ := Center(Q); O := Omega(ZQ, 2, 1);
  B := Pcgs(O); n := Length(B);
  if n > 1 then
    vz := ExponentsOfPcElement(B, z) * One(GF(2));
    compl := BaseSteinitzVectors(IdentityMat(n, GF(2)), [vz]).factorspace;
    K := Subgroup(Q, List(compl, v -> Product([1..n], i -> B[i]^IntFFE(v[i]))));
    nh := NaturalHomomorphismByNormalSubgroup(Q, K);
    Q := Image(nh); gi := List(gi, g -> Image(nh, g));
  fi;
  Print(NAME, " |Q| = 2^", LogInt(Size(Q),2), " soc rank ", n, " ords ", List(gi, Order), " s ",
        Int((Runtime()-t0)/1000), "\n");
until n <= 1;
# save a self-contained pc presentation of Q with the images of a,b,c,d (checked by check-model.g)
PrintTo(Concatenation(NAME, "-pc.g"), "# monolithic 2-quotient model ", NAME, " of order 2^", LogInt(Size(Q),2), "\n");
AppendTo(Concatenation(NAME, "-pc.g"), GapInputPcGroup(Q, "MQ"), "\n");
AppendTo(Concatenation(NAME, "-pc.g"), "MEXP := ", List(gi, g -> ExponentsOfPcElement(Pcgs(Q), g)), ";\n");
# faithful permutation model: a subgroup H with z not in H has trivial core (Q is monolithic with socle <z>);
# enlarge H greedily and act on its cosets.
if IsBound(PERM) and PERM then
  H := TrivialSubgroup(Q); Reset(GlobalMersenneTwister, 1); fails := 0;
  cand := Concatenation(gi{[2..4]}, List([1..400], i -> Random(Q)));
  for g in cand do
    K := ClosureGroup(H, g);
    if not z in K then H := K; fi;
  od;
  Print(NAME, " degree ", Index(Q, H), "\n");
  act := FactorCosetAction(Q, H); pg := List(gi, g -> Image(act, g));
  Print(NAME, " perm ords ", List(pg, Order), " relators ",
        List(rels, r -> IsOne(MappedWord(r, GeneratorsOfGroup(F), pg))), "\n");
  PrintTo(Concatenation(NAME, "-perm.g"), "# permutations a,b,c,d on ", Index(Q, H), " points\n",
          "PA := ", pg[1], ";\nPB := ", pg[2], ";\nPC := ", pg[3], ";\nPD := ", pg[4], ";\n");
fi;
QUIT;
