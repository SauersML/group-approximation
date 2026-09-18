# Calibration for the orderable-radical screen (sw-064, 2026-09-17).
# For each test (G, w) the screen/theorem predicts injectivity of G = <s> x <c | c^2>
# into (G * <t>)/<<w>>. We certify that s^j (small j) and c, s c survive by finding
# permutation representations of the one-relator quotient via low-index subgroups.
F := FreeGroup("s","c","t");; s:=F.1;; c:=F.2;; t:=F.3;;
tests := [
  ["s t c t s t^-1", s*t*c*t*s*t^-1],
  ["s c t c t s t^-2 (sum 0)", s*c*t*c*t*s*t^-2],
  ["(s c) t s^-1 t^-1", (s*c)*t*s^-1*t^-1],
  ["s t c t c t s t^-1", s*t*c*t*c*t*s*t^-1]
];;
for T in tests do
  H := F/[Comm(s,c), c^2, T[2]];;
  targets := [H.2, H.1, H.1*H.2, H.1^2*H.2, H.1^2];;
  found := List(targets, x->false);;
  for L in LowIndexSubgroupsFpGroup(H, 8) do
    hom := FactorCosetAction(H, L);;
    for i in [1..Length(targets)] do
      if not found[i] and Image(hom, targets[i]) <> () then found[i] := true; fi;
    od;
    if ForAll(found, x->x) then break; fi;
  od;
  Print(T[1], " : survive(c, s, sc, s^2 c, s^2) = ", found, "\n");
od;
QUIT;
