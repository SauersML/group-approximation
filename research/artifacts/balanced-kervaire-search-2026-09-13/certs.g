# Export explicit finite-quotient certificates for classified balanced presentations.
# For each results line "<id> <L> <r1> <r2> <verdict...>" with verdict FINITE, QUOTIENT or SIMPLE,
# write "<id> <r1> <r2> <deg> <images of x, 1-based, comma-separated> <images of y>":
# permutation images of x and y on <deg> points defining a homomorphism G -> Sym(deg).
# TRIVIAL and OPEN lines are skipped.  Verified independently by verify_certs.py.
Read("bal.g");;

PermImages := function(hom, G) local gens, deg, imgs;
  gens := GeneratorsOfGroup(G);
  imgs := List(gens, g -> Image(hom, g));
  deg := Maximum(1, LargestMovedPoint(imgs));
  return [deg, List(imgs, p -> ListPerm(p, deg))];
end;;

CertFor := function(r1, r2, verdict, maxc, maxidx) local rels, tab, G, L, k, t, e, iso, r;
  rels := [W(r1), W(r2)];
  G := F / rels;
  if StartsWith(verdict, "FINITE") then
    tab := CosetTableFromGensAndRels([x, y], rels, [] : max := maxc, silent := true);
    return [Length(tab[1]), [tab[1], tab[3]]];
  elif StartsWith(verdict, "QUOTIENT") then
    for k in LowIndexSubgroupsFpGroup(G, maxidx) do
      if Index(G, k) > 1 then return PermImages(FactorCosetAction(G, k), G); fi;
    od;
  elif StartsWith(verdict, "SIMPLE") then
    for t in TARGETS do
      if Concatenation("SIMPLE q=", t[1]) = verdict then
        e := GQuotients(G, t[2])[1];
        iso := IsomorphismPermGroup(t[2]);
        return PermImages(CompositionMapping(iso, e), G);
      fi;
    od;
  fi;
  return fail;
end;;

RunCerts := function(inpath, outpath, maxc, maxidx) local lines, ln, p, v, c;
  lines := SplitString(StringFile(inpath), "\n");
  for ln in lines do
    if ln = "" then continue; fi;
    p := SplitString(ln, " ");
    v := p[5];
    if not (StartsWith(v, "FINITE") or StartsWith(v, "QUOTIENT") or StartsWith(v, "SIMPLE")) then continue; fi;
    c := CertFor(p[3], p[4], v, maxc, maxidx);
    if c = fail then
      AppendTo(outpath, p[1], " ", p[3], " ", p[4], " FAIL\n");
    else
      AppendTo(outpath, p[1], " ", p[3], " ", p[4], " ", String(c[1]), " ",
        JoinStringsWithSeparator(List(c[2][1], String), ","), " ",
        JoinStringsWithSeparator(List(c[2][2], String), ","), "\n");
    fi;
  od;
end;;
