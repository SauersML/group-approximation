Read("tri_search.g");
A7 := AlternatingGroup(7); A8 := AlternatingGroup(8);

# Calibration: literal p,q,r in A7, pairwise generating with girth >= 6, no twist.
# The identity map is a hom into A7, so the search must report found >= 1.
CalTriple := function()
  local els7, p, q, r, tries;
  els7 := Filtered(AsList(A7), h -> Order(h) = 7);
  for tries in [1..20000] do
    p := Random(els7); q := Random(els7); r := Random(els7);
    if Size(Group(p, q)) = 2520 and Size(Group(q, r)) = 2520 and Size(Group(r, p)) = 2520
       and CosetGraphGirth(A7, Group(p), Group(q)) >= 6
       and CosetGraphGirth(A7, Group(q), Group(r)) >= 6
       and CosetGraphGirth(A7, Group(r), Group(p)) >= 6 then
      return [p, q, r];
    fi;
  od;
  return fail;
end;

cal := CalTriple();
Print("calibration triple: ", cal, "\n");
if cal <> fail then
  Run("CALIBRATION (A7,A7,A7), Euclidean",
      VData(A7, [cal[1], cal[2]]), VData(A7, [cal[2], cal[3]]), VData(A7, [cal[3], cal[1]]),
      [1, 1, 1], [A7]);
fi;

k := 0;
while k < 4 do
  k := k + 1;
  pA := FindPair(A7, 6); pB := FindPair(A7, 6); pC := FindPair(A8, 8);
  if pA = fail or pB = fail or pC = fail then Print("pair search failed\n"); continue; fi;
  e := [Random([1..6]), Random([1..6]), Random([1..6])];
  Print("cand", k, " pairs A=", pA, " B=", pB, " C=", pC, "\n");
  Run(Concatenation("CAND", String(k), " (A7,A7,A8) type (3,3,4), hyperbolic"),
      VData(A7, pA), VData(A7, pB), VData(A8, pC), e,
      [A8, AlternatingGroup(9), AlternatingGroup(10)]);
od;
Print("DONE\n");
QUIT;
