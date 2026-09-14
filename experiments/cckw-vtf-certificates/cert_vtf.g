# cert_vtf.g -- lane hl-hyperbolic-rf-2, 2026-09-14.
# Certificate export: for the CCKW group NAME (from INFILE), find with LINS the smallest-index normal
# subgroup of index <= INDEXBOUND whose quotient is injective on the three vertex groups, pass to a
# smaller-degree permutation representation of the quotient, and write the images of a, b, c and the
# relators to CERTFILE for independent verification (verify_vtf_cert.py).
# Needs INFILE, NAME, INDEXBOUND, CERTFILE.
LoadPackage("lins");
F := FreeGroup("a", "b", "c"); a := F.1; b := F.2; c := F.3;
Read(INFILE);
if IsBound(CCKWYES) then LIST := CCKWYES; else LIST := CCKW; fi;
G := First(LIST, g -> g.name = NAME);
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
Gfp := F / G.rels;
V := List(PAIRS, pr -> VertexGroup(G.rels, pr[1], pr[2]));
gr := LowIndexNormalSubgroupsSearchForAll(Gfp, INDEXBOUND);
iso := IsomorphismFpGroup(gr);
root := Grp(LinsRoot(gr));
gens := List(GeneratorsOfGroup(Gfp), g -> Image(iso, g));
best := fail;
for node in List(gr) do
  if Index(node) = 1 then continue; fi;
  hom := NaturalHomomorphismByNormalSubgroupNC(root, Grp(node));
  img := List(gens, g -> Image(hom, g));
  if ForAll([1 .. 3], k -> Size(Group(img{PAIRS[k]})) = Size(V[k].X)) then
    best := [Index(node), Image(hom), img];
    break;
  fi;
od;
if best = fail then Print("NO_CERT ", NAME, "\n"); QuitGap(1); fi;
sd := SmallerDegreePermutationRepresentation(best[2]);
Q2 := Image(sd);
img2 := List(best[3], x -> Image(sd, x));
n := LargestMovedPoint(Q2);
Print("CERT ", NAME, " index=", best[1], " |Q|=", Size(Q2), " degree=", n,
      " struct=", StructureDescription(Q2), " perfect=", IsPerfectGroup(Q2), "\n");
Print("GAP relator check: ", ForAll(G.rels, w -> MappedWord(w, GeneratorsOfGroup(F), img2) = ()), "\n");
Print("GAP vertex image orders: ", List(PAIRS, pr -> Size(Group(img2{pr}))),
      " abstract vertex orders: ", List(V, v -> Size(v.X)), "\n");
out := OutputTextFile(CERTFILE, false);
SetPrintFormattingStatus(out, false);
PrintTo(out, "name=", NAME, "\n");
AppendTo(out, "index=", best[1], "\n");
AppendTo(out, "order=", Size(Q2), "\n");
AppendTo(out, "degree=", n, "\n");
AppendTo(out, "a=", ListPerm(img2[1], n), "\n");
AppendTo(out, "b=", ListPerm(img2[2], n), "\n");
AppendTo(out, "c=", ListPerm(img2[3], n), "\n");
for w in G.rels do AppendTo(out, "rel=", w, "\n"); od;
CloseStream(out);
Print("CERT_WRITTEN ", CERTFILE, "\n");
QUIT;
