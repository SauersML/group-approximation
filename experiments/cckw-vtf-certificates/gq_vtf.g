# gq_vtf.g -- lane hl-hyperbolic-rf-2, 2026-09-14.
# For each Caprace-Conder-Kaluba-Witzel trivalent triangle group G = <a,b,c | a^3,b^3,c^3, R_ab, R_bc, R_ca>
# (arXiv:2011.09276), compute ALL epimorphisms (up to automorphisms of the target) onto each finite simple
# group that CCKW list as a quotient of G (parse_targets.py), and record the orders of the images of the
# vertex groups <a,b>, <b,c>, <c,a>.
#   SINGLE_INJ : one epimorphism is injective on all three vertex groups.
#   PRODUCT_INJ: for each vertex group V the intersection of the kernels ker(V -> S) over all
#                epimorphisms found is trivial, so the diagonal map G -> prod S is injective on
#                every vertex group.
# Either gives a finite quotient injective on the vertex groups, hence virtual torsion-freeness by
# CCKW Theorem 3.1(iv). Needs INFILE (defines CCKW), TARGETFILE (defines TARGETS); optional ONLY.
F := FreeGroup("a", "b", "c"); a := F.1; b := F.2; c := F.3;
Read(INFILE);
Read(TARGETFILE);
LIST := CCKW;
if IsBound(ONLY) then LIST := LIST{ONLY}; fi;
Letters := w -> Set(List(LetterRepAssocWord(w), AbsInt));
PAIRS := [[1, 2], [2, 3], [3, 1]];
VertexGroup := function(rels, i, j)
  local FF, rr, G0, iso, X;
  FF := FreeGroup("x", "y");
  rr := Filtered(rels, w -> IsSubset([i, j], Letters(w)));
  rr := List(rr, w -> MappedWord(w, GeneratorsOfGroup(F){[i, j]}, GeneratorsOfGroup(FF)));
  G0 := FF / rr;
  iso := IsomorphismPermGroup(G0); X := Image(iso);
  return rec(X := X, x := Image(iso, G0.1), y := Image(iso, G0.2));
end;
for G in LIST do
  t0 := Runtime();
  tr := First(TARGETS, t -> t.name = G.name);
  Gfp := F / G.rels;
  V := List(PAIRS, pr -> VertexGroup(G.rels, pr[1], pr[2]));
  Print("GROUP ", G.name, " |V|=", List(V, v -> Size(v.X)), " targets=", tr.targets, "\n");
  kers := [[], [], []];
  single := [];
  nq := 0;
  for s in tr.targets do
    S := EvalString(s);
    if not IsPermGroup(S) then S := Image(IsomorphismPermGroup(S)); fi;
    t1 := Runtime();
    epis := GQuotients(Gfp, S);
    Print("  target ", s, " |S|=", Size(S), " epimorphism classes=", Length(epis),
          " time=", Runtime() - t1, "ms\n");
    for e in epis do
      nq := nq + 1;
      img := List(GeneratorsOfGroup(Gfp), g -> Image(e, g));
      if ForAny(G.rels, w -> MappedWord(w, GeneratorsOfGroup(F), img) <> One(S)) then
        Print("  ERROR relator check failed for target ", s, "\n");
      fi;
      vs := [];
      for k in [1 .. 3] do
        phi := GroupHomomorphismByImages(V[k].X, S, [V[k].x, V[k].y], img{PAIRS[k]});
        if phi = fail then Print("  ERROR non-homomorphism on vertex ", k, "\n"); fi;
        K := Kernel(phi);
        Add(kers[k], K);
        Add(vs, Size(V[k].X) / Size(K));
      od;
      Print("    epimorphism ", nq, " onto ", s, ": vertex images=", vs, "\n");
      if ForAll([1 .. 3], k -> vs[k] = Size(V[k].X)) then
        Add(single, s);
        if NrMovedPoints(S) <= 400 then
          Print("  SINGLE_INJ_CERT target=", s, " degree=", NrMovedPoints(S),
                " a=", img[1], " b=", img[2], " c=", img[3], "\n");
        fi;
      fi;
    od;
  od;
  ikers := List([1 .. 3], k -> Size(Intersection(Concatenation([V[k].X], kers[k]))));
  Print("SUMMARY ", G.name, " epimorphisms=", nq, " SINGLE_INJ=", single,
        " kernel-intersection sizes=", ikers, " PRODUCT_INJ=", ForAll(ikers, s -> s = 1),
        " time=", Runtime() - t0, "ms\n");
od;
Print("GQ_VTF_DONE\n");
QUIT;
