# config.g -- power calibration: look for "structured" hyperbolic (A7,A7,A8) triangles with a
# KNOWN quotient. A configuration in a finite group S is (p,q,r) of order 7 with
#   <p,q> = A7 with girth(Gamma(<p,q>;<p>,<q>)) = 6,  <q,r> = A7 with girth 6,
#   <r,p> = A8 with girth 8.
# Its vertex pairs (p,q), (q,r), (r,p) define a triangle of half-girth type (3,3,4) (hyperbolic by
# CCKW Thm 3.1(v)) mapping onto <p,q,r> <= S. Search: A pairs and B pairs run over girth-6
# generating pairs of A7 up to A7-conjugacy; alpha and beta over embedding classes; r over
# double cosets exactly as in tris_lib.g CoreSearch, with the C-test replaced by the
# configuration test. Driver prepends: MODE := "sn";; NS := [..];;  or  MODE := "amb";; TARGET := "..";;
Read("tris_lib.g");
Read("girth_lib.g");
A7 := AlternatingGroup(7); A8 := AlternatingGroup(8);

Girth6Pairs := function()
  local res, c, x, ys, orbs, o, y;
  res := [];
  for c in Filtered(ConjugacyClasses(A7), c -> Order(Representative(c)) = 7) do
    x := Representative(c);
    ys := Filtered(AsList(A7), g -> Order(g) = 7);
    orbs := Orbits(Centralizer(A7, x), ys, OnPoints);
    for o in orbs do
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

# Core loop: alphas/betas are records x,y (images of a girth-6 pair), combo, pair index.
ConfigCore := function(Amb, alphas, betas, maxreport)
  local a, b, t, v, Ct, V, g0, Y, U, d, r, found, ndc;
  found := []; ndc := 0;
  for a in alphas do
    t := a.y; v := a.x;
    Ct := Centralizer(Amb, t); V := Centralizer(Ct, v);
    for b in betas do
      g0 := RepresentativeAction(Amb, b.x, t);
      if g0 <> fail then
        Y := b.y^g0;
        U := Centralizer(Ct, Group(t, Y));
        for d in DoubleCosetRepsAndSizes(Ct, U, V) do
          ndc := ndc + 1;
          r := Y^d[1];
          if IsA8Girth8(r, v) then
            Add(found, rec(p := v, q := t, r := r, acombo := a.combo, bcombo := b.combo,
                           apair := a.pair, bpair := b.pair));
            if Length(found) <= maxreport then
              Print("  CONFIG p=", v, " q=", t, " r=", r, " |<p,q,r>|=",
                    Size(Group(v, t, r)), " A=", a.combo, " B=", b.combo, "\n");
            fi;
          fi;
        od;
      fi;
    od;
  od;
  return rec(found := found, dcs := ndc);
end;

# Faster core for small targets S: betas bucketed once by the class of beta(x), with a conjugator
# to the class representative and the centraliser of the image; per alpha only a conjugation.
ConfigCoreAmb := function(S, alphas, maxreport)
  local reps, cents, bucket, b, i, gb, a, h, t, v, Ct, V, bb, Y, U, d, r, found, ndc;
  reps := List(Filtered(ConjugacyClasses(S), c -> Order(Representative(c)) = 7), Representative);
  cents := List(reps, c -> Centralizer(S, c));
  bucket := List(reps, c -> []);
  for b in alphas do
    for i in [1..Length(reps)] do
      gb := RepresentativeAction(S, b.x, reps[i]);
      if gb <> fail then
        Add(bucket[i], rec(y := b.y^gb, CB := Centralizer(S, Group(reps[i], b.y^gb)), pair := b.pair));
        break;
      fi;
    od;
  od;
  Print("  classes of 7-elements=", Length(reps), " |C(t)|=", List(cents, Size),
        " bucket sizes=", List(bucket, Length), "\n");
  found := []; ndc := 0;
  for a in alphas do
    t := a.y; v := a.x;
    for i in [1..Length(reps)] do
      h := RepresentativeAction(S, reps[i], t);
      if h <> fail then break; fi;
    od;
    Ct := cents[i]^h; V := Centralizer(Ct, v);
    for bb in bucket[i] do
      Y := bb.y^h; U := bb.CB^h;
      for d in DoubleCosetRepsAndSizes(Ct, U, V) do
        ndc := ndc + 1; r := Y^d[1];
        if IsA8Girth8(r, v) then
          Add(found, rec(p := v, q := t, r := r, apair := a.pair, bpair := bb.pair));
          if Length(found) <= maxreport then
            Print("  CONFIG p=", v, " q=", t, " r=", r, " |<p,q,r>|=", Size(Group(v, t, r)), "\n");
          fi;
        fi;
      od;
    od;
  od;
  return rec(found := found, dcs := ndc);
end;

pairs := Girth6Pairs();
Print("girth-6 generating pairs of A7 up to conjugacy: ", Length(pairs), "\n");
if MODE = "sn" then
  # Complete for the family at degree n. (natural, natural) A-set/B-set pairs are dead: then B
  # preserves the supports of the 7-cycles of q, so C = <r,p> preserves a 7-set on which p acts
  # as a 7-cycle, impossible for A8. (p,q,r) -> (r,q,p) swaps the roles of A and B and fixes C,
  # so (natural A, non-natural B) is equivalent to (non-natural A, natural B). Hence alphas run
  # over ALL A-sets and betas over A-sets with a non-natural orbit.
  for n in NS do
    t0 := Runtime(); alphas := []; betas := [];
    for k in [1..Length(pairs)] do
      V := MakeVData(A7, pairs[k]);
      for s in SetsOfDegree(TransitiveTypes(V, n), n) do
        s.pair := k; Add(alphas, s);
        if ForAny(s.combo, dd -> dd > 7) then Add(betas, s); fi;
      od;
    od;
    res := ConfigCore(SymmetricGroup(n), alphas, betas, 5);
    Print("CONFIG n=", n, " alphaSets=", Length(alphas), " betaSets(non-natural)=", Length(betas),
          " dcs=", res.dcs, " configurations=", Length(res.found), " ms=", Runtime() - t0, "\n");
  od;
else
  Read("targets.g");
  S := MakeTarget(TARGET); t0 := Runtime();
  homs := Filtered(AllHomomorphismClasses(A7, S), h -> Size(Image(h)) > 1);
  alphas := [];
  for k in [1..Length(pairs)] do
    for h in homs do
      Add(alphas, rec(x := Image(h, pairs[k][1]), y := Image(h, pairs[k][2]), combo := [], pair := k));
    od;
  od;
  res := ConfigCoreAmb(S, alphas, 5);
  Print("CONFIG ", TARGET, " A7-classes=", Length(homs), " alphas=", Length(alphas), " dcs=", res.dcs,
        " configurations=", Length(res.found), " ms=", Runtime() - t0, "\n");
fi;
Print("CONFIG_DONE\n");
QUIT;
