# cckw_compat.g -- edge-eigenvalue compatibility filter for vertex-faithful linear representations of the
# 19 CCKW (6,6,8) groups (cckw334.g). A homomorphism G -> GL_d(C) that is faithful and irreducible on each
# vertex group restricts to faithful irreducible characters chi_ab, chi_bc, chi_ca of degree d, and each
# edge generator must have the same eigenvalue multiplicities in the two vertex modules containing it:
#   eig_b(chi_ab) = eig_b(chi_bc), eig_c(chi_bc) = eig_c(chi_ca), eig_a(chi_ca) = eig_a(chi_ab).
# Counts the compatible triples for d = 2..6 (necessary condition only; compatible triples still need the
# trace-ideal test).
Read("girth_lib.g");
F := FreeGroup("a", "b", "c"); a := F.1; b := F.2; c := F.3;
Read("cckw334.g");
Letters := w -> Set(List(LetterRepAssocWord(w), AbsInt));
EigMult := function(chi, g, X)
  local cls, pos;
  cls := ConjugacyClasses(X);
  pos := j -> PositionProperty(cls, cl -> g^j in cl);
  return List([0..2], k -> Sum([0..2], j -> chi[pos(j)] * E(3)^(-k*j)) / 3);
end;
Faithful := function(rels, i, j, d)
  local FF, rr, G0, iso, X, x, y, chis;
  FF := FreeGroup("x", "y");
  rr := Filtered(rels, w -> IsSubset([i, j], Letters(w)));
  rr := List(rr, w -> MappedWord(w, GeneratorsOfGroup(F){[i, j]}, GeneratorsOfGroup(FF)));
  G0 := FF / rr; iso := IsomorphismPermGroup(G0); X := Image(iso);
  x := Image(iso, G0.1); y := Image(iso, G0.2);
  chis := Filtered(Irr(X), chi -> chi[1] = d and Size(KernelOfCharacter(chi)) = 1);
  return List(chis, chi -> rec(ex := EigMult(chi, x, X), ey := EigMult(chi, y, X)));
end;
for G in CCKW do
  line := [];
  for d in [2..6] do
    AB := Faithful(G.rels, 1, 2, d);   # x = a, y = b
    BC := Faithful(G.rels, 2, 3, d);   # x = b, y = c
    CA := Faithful(G.rels, 3, 1, d);   # x = c, y = a
    n := 0;
    for u in AB do for v in BC do for w in CA do
      if u.ey = v.ex and v.ey = w.ex and w.ey = u.ex then n := n + 1; fi;
    od; od; od;
    Add(line, [d, Length(AB), Length(BC), Length(CA), n]);
  od;
  Print(G.name, " [d, #faithful irreps at ab, bc, ca, #compatible triples]: ", line, "\n");
od;
Print("CCKW_COMPAT_DONE\n");
QUIT;
