Read("tri334_lib.g");
# Calibration of the face-consistency count: the same code with X0 replaced by L3(2) (type (3,3,3),
# chamber-transitive A~2 amalgams, which exist). Expect some consistent triples.
V := Filtered(Elements(GF(2)^3), v -> not IsZero(v));
X1 := Action(SL(3,2), V, OnRight);
k := Position(V, V[1] + V[2]);
P1 := Stabilizer(X1, 1); L1 := Stabilizer(X1, Set([1, 2, k]), OnSets); B1 := Intersection(P1, L1);
Count := function(P0, L0, B0)
  local a, b, c, E001, E002, E101, E112, E202, E212, I01, I02, I12, n, h01, h02, h12, out;
  out := [];
  for a in [1,2] do for b in [1,2] do for c in [1,2] do
    E001 := [P0, L0][a]; E002 := [P0, L0][3 - a];
    E101 := [P1, L1][b]; E112 := [P1, L1][3 - b];
    E202 := [P1, L1][c]; E212 := [P1, L1][3 - c];
    I01 := IsosMappingFace(E001, E101, B0, B1); I02 := IsosMappingFace(E002, E202, B0, B1);
    I12 := IsosMappingFace(E112, E212, B1, B1);
    n := 0;
    for h01 in I01 do for h02 in I02 do for h12 in I12 do
      if ForAll(GeneratorsOfGroup(B0), x -> Image(h12, Image(h01, x)) = Image(h02, x)) then n := n + 1; fi;
    od; od; od;
    Add(out, [[a,b,c], n]);
  od; od; od;
  return out;
end;
Print("(L3(2),L3(2),L3(2)) consistent triples per pattern: ", Count(P1, L1, B1), "\n");
# Holonomy diagnostics for (A6,L3(2),L3(2)): images in Out(D8) of the base restrictions.
X0 := AlternatingGroup(6);
P0 := Stabilizer(X0, [1,2], OnSets);
L0 := Stabilizer(X0, Set([Set([1,2]), Set([3,4]), Set([5,6])]), OnSetsSets);
B0 := Intersection(P0, L0);
Print("(A6,L3(2),L3(2)) consistent triples per pattern: ", Count(P0, L0, B0), "\n");
Print("IdGroup B0, B1: ", IdGroup(B0), IdGroup(B1), "\n");
Print("DONE\n");
QUIT;
