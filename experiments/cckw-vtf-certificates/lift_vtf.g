# lift_vtf.g -- lane hl-hyperbolic-rf-2, 2026-09-14.
# For the Caprace-Conder-Kaluba-Witzel trivalent triangle group of spec SPECINDEX in SPECFILE and each cover
# in its list, form a quasisimple group H (a matrix group given by a GAP expression such as "SL(2,49)", or
# 2.A_n as the derived subgroup of GAP's basic spin representation of 2.S_n), the central quotient
# S = H/Z(H) as a permutation group, and all epimorphisms G -> S up to Aut(S) (GQuotients). A lift of
# such an epimorphism to H sends a, b, c to preimages of order 3 (a^3 = b^3 = c^3 = 1 are relators), so
# the lifts are enumerated over Z(H), kept if every relator holds, and tested for injectivity on the
# vertex groups <a,b>, <b,c>, <c,a>. A vertex-injective lift is exported as a permutation certificate in
# the format of verify_vtf_cert.py. Needs SPECFILE, SPECINDEX set before Read.
F := FreeGroup("a", "b", "c"); a := F.1; b := F.2; c := F.3;
Read(SPECFILE);
SPEC := LIFTSPECS[SPECINDEX];
Read(SPEC.infile);
if IsBound(CCKWYES) then LIST := CCKWYES; else LIST := CCKW; fi;
G := First(LIST, g -> g.name = SPEC.name);
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
vord := List(V, v -> Size(v.X));
Print("GROUP ", G.name, " |V|=", vord, " covers=", List(SPEC.covers, cs -> cs.name), "\n");
ncert := 0;
for cs in SPEC.covers do
  t0 := Runtime();
  if cs.kind = "matrix" then
    H := EvalString(cs.expr);
  else
    H := DerivedSubgroup(Group(BasicSpinRepresentationOfSymmetricGroup(cs.n, cs.p, 1)));
  fi;
  ZH := Centre(H);
  pi := NaturalHomomorphismByNormalSubgroup(H, ZH);
  if not IsPermGroup(Image(pi)) then pi := pi * IsomorphismPermGroup(Image(pi)); fi;
  S := Image(pi);
  Print("  cover ", cs.name, " |H|=", Size(H), " |Z|=", Size(Z), " |H/Z|=", Size(S),
        " setup time=", Runtime() - t0, "ms\n");
  t0 := Runtime();
  epis := GQuotients(Gfp, S);
  Print("    epimorphism classes onto H/Z: ", Length(epis), " time=", Runtime() - t0, "ms\n");
  zs := Elements(Z);
  nlift := 0;
  for e in epis do
    img := List(GeneratorsOfGroup(Gfp), g -> Image(e, g));
    cand := List(img, x -> Filtered(List(zs, z -> PreImagesRepresentative(pi, x) * z), y -> IsOne(y ^ 3)));
    for ta in cand[1] do for tb in cand[2] do for tc in cand[3] do
      L := [ta, tb, tc];
      if ForAll(G.rels, w -> IsOne(MappedWord(w, GeneratorsOfGroup(F), L))) then
        nlift := nlift + 1;
        vs := List(PAIRS, pr -> Size(Group(L{pr})));
        Print("    lift ", nlift, ": vertex images=", vs, "\n");
        if vs = vord then
          ncert := ncert + 1;
          K := Group(L);
          nm := IsomorphismPermGroup(K);
          sd := SmallerDegreePermutationRepresentation(Image(nm));
          P := List(L, x -> Image(sd, Image(nm, x)));
          n := Maximum(List(P, LargestMovedPoint));
          Print("  VERTEX_INJECTIVE_LIFT cover=", cs.name, " |image|=", Size(K), " export degree=", n, "\n");
          if n <= 40000 then
            fn := Concatenation(SPEC.tag, "_lift", String(ncert), ".cert");
            out := OutputTextFile(Concatenation("certs/", fn), false);
            SetPrintFormattingStatus(out, false);
            PrintTo(out, "name=", G.name, "\n");
            AppendTo(out, "targets=", cs.name, " lift\n");
            AppendTo(out, "degree=", n, "\n");
            AppendTo(out, "a=", ListPerm(P[1], n), "\n");
            AppendTo(out, "b=", ListPerm(P[2], n), "\n");
            AppendTo(out, "c=", ListPerm(P[3], n), "\n");
            for w in G.rels do AppendTo(out, "rel=", w, "\n"); od;
            CloseStream(out);
            Print("  CERT_WRITTEN certs/", fn, "\n");
          fi;
        fi;
      fi;
    od; od; od;
  od;
  Print("    lifts satisfying all relators: ", nlift, "\n");
  if ncert > 0 then break; fi;
od;
Print("LIFT_SUMMARY ", G.name, " vertex-injective lifts=", ncert, "\n");
Print("LIFT_VTF_DONE\n");
QUIT;
