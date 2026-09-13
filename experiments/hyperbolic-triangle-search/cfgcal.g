# cfgcal.g -- calibration of config.g (same pair list, same double-coset core, own C-test hook).
# (U1) each candidate's C pair passes IsA8Girth8; (U2) each candidate's A and B pair is
# A7-conjugate to a listed girth-6 pair; (P) positive control: with the C-test replaced by
# "<r,p> = A7 with girth 6", the enumeration over degree-15 A7-sets in S_15 finds the literal
# (A7,A7,A7) triple of tri_cal2.g acting on 15 points.
Read("tris_lib.g");
Read("girth_lib.g");
Read("cands.g");
A7 := AlternatingGroup(7); A8 := AlternatingGroup(8);
Girth6Pairs := function()
  local res, c, x, o, y;
  res := [];
  for c in Filtered(ConjugacyClasses(A7), c -> Order(Representative(c)) = 7) do
    x := Representative(c);
    for o in Orbits(Centralizer(A7, x), Filtered(AsList(A7), g -> Order(g) = 7), OnPoints) do
      y := o[1];
      if Size(Group(x, y)) = 2520 and CosetGraphGirth(A7, Group(x), Group(y)) = 6 then
        Add(res, [x, y]);
      fi;
    od;
  od;
  return res;
end;
OrdSet8 := [1, 2, 3, 4, 5, 6, 7, 15];
IsA8Girth8 := function(r, p)
  local H;
  if not (Order(r*p) in OrdSet8 and Order(r*p^-1) in OrdSet8 and Order(r^2*p) in OrdSet8
          and Order(r*p^2) in OrdSet8 and Order(Comm(r, p)) in OrdSet8
          and Order(r*p*r*p^3) in OrdSet8) then return false; fi;
  H := Group(r, p);
  if Size(H) <> 20160 or not 15 in List(ConjugacyClasses(H), c -> Order(Representative(c))) then
    return false;
  fi;
  return CosetGraphGirth(H, Group(r), Group(p)) = 8;
end;
OrdSet7 := [1, 2, 3, 4, 5, 6, 7];
IsA7Girth6 := function(r, p)
  local H;
  if not (Order(r*p) in OrdSet7 and Order(r*p^-1) in OrdSet7 and Order(r^2*p) in OrdSet7
          and Order(r*p^2) in OrdSet7 and Order(Comm(r, p)) in OrdSet7) then return false; fi;
  H := Group(r, p);
  return Size(H) = 2520 and IsSimple(H) and CosetGraphGirth(H, Group(r), Group(p)) = 6;
end;
ConfigCoreT := function(Amb, alphas, betas, test)
  local a, b, t, v, Ct, V, g0, Y, U, d, r, found;
  found := 0;
  for a in alphas do
    t := a.y; v := a.x; Ct := Centralizer(Amb, t); V := Centralizer(Ct, v);
    for b in betas do
      g0 := RepresentativeAction(Amb, b.x, t);
      if g0 <> fail then
        Y := b.y^g0; U := Centralizer(Ct, Group(t, Y));
        for d in DoubleCosetRepsAndSizes(Ct, U, V) do
          r := Y^d[1];
          if test(r, v) then found := found + 1; fi;
        od;
      fi;
    od;
  od;
  return found;
end;
pairs := Girth6Pairs();
Print("pairs=", Length(pairs), "\n");
for k in [1..4] do
  c := cands[k];
  Print("U1 CAND", k, " C pair girth-8 A8: ", IsA8Girth8(c.C[1], c.C[2]), "\n");
  for P in [c.A, c.B] do
    Print("U2 CAND", k, " pair conjugate into list: ",
          ForAny(pairs, pr -> RepresentativeAction(A7, P, pr, OnTuples) <> fail), "\n");
  od;
od;
t0 := Runtime(); alphas := [];
for k in [1..Length(pairs)] do
  for s in SetsOfDegree(TransitiveTypes(MakeVData(A7, pairs[k]), 15), 15) do
    if s.combo = [15] then Add(alphas, s); fi;
  od;
od;
nf := ConfigCoreT(SymmetricGroup(15), alphas, alphas, IsA7Girth6);
Print("P (A7,A7,A7) configurations in S_15 over 15-point A7-sets: ", nf, " (must be >= 1) ms=",
      Runtime() - t0, "\n");
Print("CFGCAL_DONE\n");
QUIT;
