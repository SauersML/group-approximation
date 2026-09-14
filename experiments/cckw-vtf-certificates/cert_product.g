# cert_product.g -- lane hl-hyperbolic-rf-2, 2026-09-14.
# Certificate export for a Caprace-Conder-Kaluba-Witzel trivalent triangle group NAME: run over the
# epimorphisms onto the simple quotients CCKW list (TARGETFILE), greedily keep an epimorphism whenever it
# shrinks the intersection of kernels on some vertex group, and stop once all three intersections are
# trivial. The kept epimorphisms act on disjoint point sets; concatenating them gives one homomorphism
# G -> S_degree that is injective on every vertex group. Writes a, b, c and the relators to CERTFILE in the
# format read by verify_vtf_cert.py. Needs INFILE, TARGETFILE, NAME, CERTFILE.
F := FreeGroup("a", "b", "c"); a := F.1; b := F.2; c := F.3;
Read(INFILE);
Read(TARGETFILE);
if IsBound(CCKWYES) then LIST := CCKWYES; else LIST := CCKW; fi;
G := First(LIST, g -> g.name = NAME);
tr := First(TARGETS, t -> t.name = NAME);
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
cur := List(V, v -> v.X);
chosen := [];
done := false;
for s in tr.targets do
  S := EvalString(s);
  if not IsPermGroup(S) then S := Image(IsomorphismPermGroup(S)); fi;
  for e in GQuotients(Gfp, S) do
    img := List(GeneratorsOfGroup(Gfp), g -> Image(e, g));
    Ks := List([1 .. 3], k -> Kernel(GroupHomomorphismByImages(V[k].X, S, [V[k].x, V[k].y], img{PAIRS[k]})));
    new := List([1 .. 3], k -> Intersection(cur[k], Ks[k]));
    if ForAny([1 .. 3], k -> Size(new[k]) < Size(cur[k])) then
      Add(chosen, rec(target := s, img := img, n := LargestMovedPoint(S)));
      cur := new;
      Print("  kept epimorphism onto ", s, " (degree ", LargestMovedPoint(S), "); kernel intersections now ",
            List(cur, Size), "\n");
    fi;
    if ForAll(cur, k -> Size(k) = 1) then done := true; break; fi;
  od;
  if done then break; fi;
od;
if not done then Print("NO_CERT ", NAME, " kernel intersections ", List(cur, Size), "\n"); QuitGap(1); fi;
shift := 0;
lists := [[], [], []];
for ch in chosen do
  for k in [1 .. 3] do
    Append(lists[k], List(ListPerm(ch.img[k], ch.n), i -> i + shift));
  od;
  shift := shift + ch.n;
od;
perms := List(lists, PermList);
Print("CERT ", NAME, " targets=", List(chosen, ch -> ch.target), " degree=", shift, "\n");
Print("GAP relator check: ", ForAll(G.rels, w -> MappedWord(w, GeneratorsOfGroup(F), perms) = ()), "\n");
Print("GAP vertex image orders: ", List(PAIRS, pr -> Size(Group(perms{pr}))),
      " abstract vertex orders: ", List(V, v -> Size(v.X)), "\n");
out := OutputTextFile(CERTFILE, false);
SetPrintFormattingStatus(out, false);
PrintTo(out, "name=", NAME, "\n");
AppendTo(out, "targets=", List(chosen, ch -> ch.target), "\n");
AppendTo(out, "degree=", shift, "\n");
AppendTo(out, "a=", lists[1], "\n");
AppendTo(out, "b=", lists[2], "\n");
AppendTo(out, "c=", lists[3], "\n");
for w in G.rels do AppendTo(out, "rel=", w, "\n"); od;
CloseStream(out);
Print("CERT_WRITTEN ", CERTFILE, "\n");
QUIT;
