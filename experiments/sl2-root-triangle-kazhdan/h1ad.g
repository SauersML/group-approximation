# h1ad.g -- first-order deformations of rho: Lambda_0 -> SL_2(q^2) (untwisted Kazhdan SL_2 root triangle).
# Computes dim over F = GF(q^2) of H^1(G; M) by Fox calculus from the presentation of untw.g, for
#   M = natural F^2,  sl_2(F) = trace-zero 2x2 matrices (conjugation),  gl_2(F) (conjugation),
# both for G = Lambda_0 (through rho) and for G = SL_2(q^2) itself (presentation on u(F_q), v(sF_q) plus
# nothing else: that presentation is the A_3 vertex group). A cocycle with values in sl_2 is a deformation
# (1 + t d) rho into SL_2(F[t]/t^2); H^1 beyond the SL_2(q^2) part is new congruence structure of Lambda_0.
H1Dim := function(G, imgs, act, dimM, F)
  local gens, r, rels, eqs, w, rep, i, prefix, g, sgn, row, blk, pos, sys, nsp, M0, bdry;
  gens := GeneratorsOfGroup(FreeGroupOfFpGroup(G)); r := Length(gens);
  rels := RelatorsOfFpGroup(G);
  eqs := [];
  for w in rels do
    rep := LetterRepAssocWord(w);
    row := NullMat(dimM, r * dimM, F);                 # d(w) = sum over letters of prefix . (+-) d(gen)
    prefix := IdentityMat(dimM, F);
    for i in rep do
      g := AbsInt(i);
      if i > 0 then
        blk := prefix;
        prefix := prefix * act(imgs[g]);
      else
        prefix := prefix * act(imgs[g]^-1);
        blk := -prefix;
      fi;
      pos := (g - 1) * dimM;
      row{[1..dimM]}{[pos+1..pos+dimM]} := row{[1..dimM]}{[pos+1..pos+dimM]} + blk;
    od;
    Append(eqs, row);
  od;
  sys := ImmutableMatrix(F, eqs);
  nsp := r * dimM - RankMat(sys);                        # dim Z^1
  M0 := Concatenation(List(imgs, x -> act(x) - IdentityMat(dimM, F)));   # invariants = kernel of stacked (g - 1)
  bdry := dimM - (dimM - RankMat(M0));                   # dim B^1 = dim M - dim M^G
  return [nsp, bdry, nsp - bdry];
end;
RunDef := function(f)
  local q, Q, F, s, bas, u, v, P, e12, A1gens, A3gens, iso1, iso3, rel1, rel3, fr, a, b, c, rels, G, imgs,
        natural, conj, slbasis, slact, G3, imgs3, t;
  q := 2^f; Q := q^2; F := GF(Q); s := Z(Q);
  bas := List([0..f-1], i -> Z(q)^i);
  u := x -> [[One(F), x], [Zero(F), One(F)]]; v := x -> [[One(F), Zero(F)], [x, One(F)]];
  P := (s^-1)^(Q/2);
  e12 := x -> [[One(F) + P*x, P^2*x], [x, One(F) + P*x]];
  A1gens := Concatenation(List(bas, u), List(bas, v));
  A3gens := Concatenation(List(bas, u), List(bas, x -> v(s*x)));
  iso1 := IsomorphismFpGroupByGenerators(Group(A1gens), A1gens);
  iso3 := IsomorphismFpGroupByGenerators(Group(A3gens), A3gens);
  rel1 := RelatorsOfFpGroup(Range(iso1)); rel3 := RelatorsOfFpGroup(Range(iso3));
  fr := FreeGroup(3*f);
  a := GeneratorsOfGroup(fr){[1..f]}; b := GeneratorsOfGroup(fr){[f+1..2*f]}; c := GeneratorsOfGroup(fr){[2*f+1..3*f]};
  rels := Concatenation(
    List(rel1, r -> MappedWord(r, FreeGeneratorsOfFpGroup(Range(iso1)), Concatenation(a, b))),
    List(rel1, r -> MappedWord(r, FreeGeneratorsOfFpGroup(Range(iso1)), Concatenation(a, c))),
    List(rel3, r -> MappedWord(r, FreeGeneratorsOfFpGroup(Range(iso3)), Concatenation(b, c))));
  G := fr / rels;
  imgs := Concatenation(List(bas, e12), List(bas, u), List(bas, x -> v(s*x)));
  # all actions are LEFT actions on column vectors: act(gh) = act(g) act(h); Fox: d(xy) = d(x) + x.d(y)
  natural := x -> x;
  conj := function(x)                                    # m -> x m x^-1 on gl_2, basis E11,E12,E21,E22, images as columns
    local B, E; B := IdentityMat(4, F);
    E := List(B, e -> [[e[1], e[2]], [e[3], e[4]]]);
    return TransposedMat(List(E, m -> Flat(x * m * x^-1)));
  end;
  slbasis := [[[One(F), Zero(F)], [Zero(F), One(F)]], [[Zero(F), One(F)], [Zero(F), Zero(F)]], [[Zero(F), Zero(F)], [One(F), Zero(F)]]];
  slact := function(x)                                   # m -> x m x^-1 on trace-zero matrices (contains I in char 2)
    return TransposedMat(List(slbasis, m -> SolutionMat(List(slbasis, Flat), Flat(x * m * x^-1))));
  end;
  Assert(0, ForAll([1..Length(imgs)], i -> slact(imgs[i]) * slact(imgs[1]) = slact(imgs[i] * imgs[1])));
  G3 := Range(iso3); imgs3 := A3gens;
  t := Runtime();
  Print("q=", q, "  [dim Z^1, dim B^1, dim H^1] over GF(", Q, "):\n");
  Print("  Lambda_0   natural ", H1Dim(G, imgs, natural, 2, F),
        "  sl_2 ", H1Dim(G, imgs, slact, 3, F), "  gl_2 ", H1Dim(G, imgs, conj, 4, F), "\n");
  Print("  SL_2(", Q, ") natural ", H1Dim(G3, imgs3, natural, 2, F),
        "  sl_2 ", H1Dim(G3, imgs3, slact, 3, F), "  gl_2 ", H1Dim(G3, imgs3, conj, 4, F), "  (", Runtime() - t, " ms)\n");
end;
RunDef(2);
RunDef(3);
Print("DONE\n");
QUIT;
