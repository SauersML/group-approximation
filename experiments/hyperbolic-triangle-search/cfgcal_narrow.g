# cfgcal_narrow.g -- fast positive control for config.g: the same pair list, A7-set construction and
# double-coset core, restricted to the listed pairs conjugate to the literal (A7,A7,A7) triple's pairs
# (p,q) and (q,r) of tri_cal2.g, over 15-point A7-sets, with the C-test "<r,p> = A7 with girth 6".
# The literal triple composed with a 15-point action of A7 is such a configuration, so found >= 1.
Read("tris_lib.g");
Read("girth_lib.g");
A7 := AlternatingGroup(7);
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
OrdSet7 := [1, 2, 3, 4, 5, 6, 7];
IsA7Girth6 := function(r, p)
  local H;
  if not (Order(r*p) in OrdSet7 and Order(r*p^-1) in OrdSet7 and Order(r^2*p) in OrdSet7
          and Order(r*p^2) in OrdSet7 and Order(Comm(r, p)) in OrdSet7) then return false; fi;
  H := Group(r, p);
  return Size(H) = 2520 and IsSimple(H) and CosetGraphGirth(H, Group(r), Group(p)) = 6;
end;
ConfigCoreT := function(Amb, alphas, betas, test)
  local a, b, t, v, Ct, V, g0, Y, U, d, r, found, ndc;
  found := 0; ndc := 0;
  for a in alphas do
    t := a.y; v := a.x; Ct := Centralizer(Amb, t); V := Centralizer(Ct, v);
    for b in betas do
      g0 := RepresentativeAction(Amb, b.x, t);
      if g0 <> fail then
        Y := b.y^g0; U := Centralizer(Ct, Group(t, Y));
        for d in DoubleCosetRepsAndSizes(Ct, U, V) do
          ndc := ndc + 1; r := Y^d[1];
          if test(r, v) then found := found + 1; fi;
        od;
      fi;
    od;
  od;
  return [found, ndc];
end;
cal := [ (1,7,4,6,5,2,3), (1,2,4,7,6,3,5), (1,6,3,2,7,4,5) ];
Print("literal pair girths: ", CosetGraphGirth(A7, Group(cal[1]), Group(cal[2])), " ",
      CosetGraphGirth(A7, Group(cal[2]), Group(cal[3])), " ", CosetGraphGirth(A7, Group(cal[3]), Group(cal[1])), "\n");
pairs := Girth6Pairs();
k1 := First([1..Length(pairs)], k -> RepresentativeAction(A7, [cal[1], cal[2]], pairs[k], OnTuples) <> fail);
k2 := First([1..Length(pairs)], k -> RepresentativeAction(A7, [cal[2], cal[3]], pairs[k], OnTuples) <> fail);
Print("pairs=", Length(pairs), " k1=", k1, " k2=", k2, "\n");
t0 := Runtime();
alphas := Filtered(SetsOfDegree(TransitiveTypes(MakeVData(A7, pairs[k1]), 15), 15), s -> s.combo = [15]);
betas := Filtered(SetsOfDegree(TransitiveTypes(MakeVData(A7, pairs[k2]), 15), 15), s -> s.combo = [15]);
res := ConfigCoreT(SymmetricGroup(15), alphas, betas, IsA7Girth6);
Print("PNARROW alphas=", Length(alphas), " betas=", Length(betas), " dcs=", res[2], " found=", res[1],
      " (must be >= 1) ms=", Runtime() - t0, "\n");
# Negative control on the same slice: the A8-girth-8 test cannot pass when <r,p> is an A7.
Print("CFGCAL_NARROW_DONE\n");
QUIT;
