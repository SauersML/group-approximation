# zds n = 22 survivor analysis: the group <x, y | cycle words> of each surviving labelling.
# Input surv22rels.g sets ZdsSurv, a list of relator lists in the letters x X y Y.
F := FreeGroup("x", "y");;
ZdsWord := function(s)
  local w, c;
  w := One(F);
  for c in s do
    if c = 'x' then w := w * F.1;
    elif c = 'X' then w := w * F.1^-1;
    elif c = 'y' then w := w * F.2;
    else w := w * F.2^-1; fi;
  od;
  return w;
end;;
Read("surv22rels.g");;
Print("survivors: ", Length(ZdsSurv), "\n");
for i in [1..Length(ZdsSurv)] do
  rels := List(ZdsSurv[i], ZdsWord);;
  G := F / rels;;
  Print("== ", i, " abelian invariants ", AbelianInvariants(G), "\n");
  ct := CosetTableFromGensAndRels(GeneratorsOfGroup(F), rels, [] : max := 4000000, silent := true);;
  if ct = fail then
    Print("  enumeration over the trivial subgroup exceeds 4000000 cosets\n");
  else
    px := PermList(ct[1]);; py := PermList(ct[3]);;
    Print("  FINITE of order ", Length(ct[1]), "; orders x ", Order(px), " y ", Order(py),
          " x^-1 y ", Order(px^-1 * py), "\n");
  fi;
  iso := IsomorphismSimplifiedFpGroup(G);;
  S := Range(iso);;
  Print("  simplified: ", Length(GeneratorsOfGroup(S)), " generators, relator lengths ",
        List(RelatorsOfFpGroup(S), Length), "\n");
  L := LowIndexSubgroupsFpGroup(G, 6);;
  Print("  index <= 6: ", List(L, H -> [ Index(G, H), AbelianInvariants(H) ]), "\n");
od;
Print("GAPDONE\n");
QUIT;
