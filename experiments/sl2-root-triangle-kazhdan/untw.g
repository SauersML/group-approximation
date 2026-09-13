# untw.g -- model test of sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2, and calibration data.
# Builds the colimit Lambda_0 of the untwisted SL_2 root triangle (SL_2(q), SL_2(q), SL_2(q^2)) as a finitely
# presented group (generators: F_2-bases of the three edge groups; relators: presentations of the three vertex
# groups in those generators), checks that h = [[P,1],[1,0]], h u(1/P), id (P^2 = 1/s) define a homomorphism
# onto SL_2(q^2), and for q = 4 computes H_1 of its kernel (to calibrate moment2.py).
RunQ := function(f, doAb)
  local q, Q, F, s, k, bas, u, v, P, e12, A1gens, A3gens, iso1, iso3, rel1, rel3, G, fr, a, b, c,
        rels, imgs, hom, K, t, S;
  q := 2^f; Q := q^2; F := GF(Q); s := Z(Q);
  bas := List([0..f-1], i -> Z(q)^i);          # spans F_q over F_2 for f <= 4 (checked below)
  Assert(0, Size(VectorSpace(GF(2), bas)) = q);
  u := x -> [[One(F), x], [Zero(F), One(F)]];
  v := x -> [[One(F), Zero(F)], [x, One(F)]];
  P := (s^-1)^(Q/2);
  Assert(0, P^2 * s = One(F));
  e12 := x -> [[One(F) + P*x, P^2*x], [x, One(F) + P*x]];   # h u(x) h^-1
  A1gens := Concatenation(List(bas, u), List(bas, v));                 # SL_2(q): u(F_q), v(F_q)
  A3gens := Concatenation(List(bas, u), List(bas, x -> v(s*x)));       # SL_2(q^2): u(F_q), v(sF_q)
  iso1 := IsomorphismFpGroupByGenerators(Group(A1gens), A1gens);
  iso3 := IsomorphismFpGroupByGenerators(Group(A3gens), A3gens);
  Assert(0, Size(Group(A1gens)) = q*(q^2-1) and Size(Group(A3gens)) = Q*(Q^2-1));
  rel1 := RelatorsOfFpGroup(Range(iso1)); rel3 := RelatorsOfFpGroup(Range(iso3));
  fr := FreeGroup(3*f);
  a := GeneratorsOfGroup(fr){[1..f]}; b := GeneratorsOfGroup(fr){[f+1..2*f]}; c := GeneratorsOfGroup(fr){[2*f+1..3*f]};
  rels := Concatenation(
    List(rel1, r -> MappedWord(r, FreeGeneratorsOfFpGroup(Range(iso1)), Concatenation(a, b))),   # A_1: E_12 = u, E_13 = v
    List(rel1, r -> MappedWord(r, FreeGeneratorsOfFpGroup(Range(iso1)), Concatenation(a, c))),   # A_2: E_12 = u, E_23 = v
    List(rel3, r -> MappedWord(r, FreeGeneratorsOfFpGroup(Range(iso3)), Concatenation(b, c))));  # A_3: E_13 = u, E_23 = v(s.)
  G := fr / rels;
  imgs := Concatenation(List(bas, e12), List(bas, u), List(bas, x -> v(s*x)));
  S := SL(2, Q);
  hom := GroupHomomorphismByImages(G, S, GeneratorsOfGroup(G), imgs);
  Print("q=", q, " relators ", Length(rels), " homomorphism: ", hom <> fail, "\n");
  if hom <> fail then
    Print("  onto SL_2(", Q, "): ", Size(Image(hom)) = Size(S), "\n");
    if doAb then
      t := Runtime(); K := Kernel(hom);
      Print("  index ", Index(G, K), "  H_1(kernel;Z) invariants ", AbelianInvariants(K), "  (", Runtime() - t, " ms)\n");
    fi;
  fi;
end;
RunQ(2, true);
RunQ(3, false);
RunQ(4, false);
Print("DONE\n");
QUIT;
