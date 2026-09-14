# lins_vtf.g -- lane hl-hyperbolic-rf-2, 2026-09-14.
# For each Caprace-Conder-Kaluba-Witzel trivalent triangle group G = <a,b,c | a^3,b^3,c^3, R_ab, R_bc, R_ca>
# (arXiv:2011.09276, presentations_3_3_4.tex, converted by cckw_convert.py), enumerate ALL normal
# subgroups of index <= INDEXBOUND with the LINS package, and for each quotient Q = G/H record the
# orders of the images of the three vertex groups <a,b>, <b,c>, <c,a>.
#   SINGLE_INJ : some Q is injective on all three vertex groups.
#   PRODUCT_INJ: for each vertex group V the intersection over all found Q of ker(V -> Q) is trivial,
#                so G -> prod Q is injective on all three vertex groups.
# Either gives a finite quotient injective on the vertex groups, hence virtual torsion-freeness by
# CCKW Theorem 3.1(iv). Needs: INFILE (defines LIST via CCKW or CCKWYES), INDEXBOUND, set before Read.
LoadPackage("lins");
F := FreeGroup("a", "b", "c"); a := F.1; b := F.2; c := F.3;
Read(INFILE);
if IsBound(CCKWYES) then LIST := CCKWYES; else LIST := CCKW; fi;
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
  Gfp := F / G.rels;
  V := List(PAIRS, pr -> VertexGroup(G.rels, pr[1], pr[2]));
  Print("GROUP ", G.name, " |V|=", List(V, v -> Size(v.X)), " bound=", INDEXBOUND, "\n");
  gr := LowIndexNormalSubgroupsSearchForAll(Gfp, INDEXBOUND);
  iso := IsomorphismFpGroup(gr);
  root := Grp(LinsRoot(gr));
  gens := List(GeneratorsOfGroup(Gfp), g -> Image(iso, g));
  kers := [[], [], []];
  single := [];
  nq := 0;
  for node in List(gr) do
    if Index(node) = 1 then continue; fi;
    nq := nq + 1;
    hom := NaturalHomomorphismByNormalSubgroupNC(root, Grp(node));
    Q := Image(hom);
    img := List(gens, g -> Image(hom, g));
    vs := [];
    for k in [1 .. 3] do
      phi := GroupHomomorphismByImages(V[k].X, Q, [V[k].x, V[k].y], img{PAIRS[k]});
      if phi = fail then Print("  ERROR non-homomorphism at index ", Index(node), "\n"); fi;
      K := Kernel(phi);
      Add(kers[k], K);
      Add(vs, Size(V[k].X) / Size(K));
    od;
    if Size(Q) <= 3000 then desc := StructureDescription(Q);
    else desc := Concatenation("order ", String(Size(Q)), " simple=", String(IsSimpleGroup(Q)),
                               " solvable=", String(IsSolvableGroup(Q)));
    fi;
    Print("  Q index=", Index(node), " vertex images=", vs, " ", desc, "\n");
    if ForAll([1 .. 3], k -> vs[k] = Size(V[k].X)) then
      Add(single, Index(node));
      Print("  SINGLE_INJ_CERT index=", Index(node), " degree=", NrMovedPoints(Q),
            " a=", img[1], " b=", img[2], " c=", img[3], "\n");
    fi;
  od;
  ikers := List([1 .. 3], k -> Size(Intersection(Concatenation([V[k].X], kers[k]))));
  Print("SUMMARY ", G.name, " quotients=", nq, " SINGLE_INJ=", single,
        " kernel-intersection sizes=", ikers, " PRODUCT_INJ=", ForAll(ikers, s -> s = 1),
        " time=", Runtime() - t0, "ms\n");
od;
Print("LINS_VTF_DONE\n");
QUIT;
