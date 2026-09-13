# Triangles of groups G = <p,q,r | R_A(p,q), R_B(q^e1,r), R_C(r^e2,p^e3)>: vertex groups
# A=<p,q>, B=<q,r>, C=<r,p> finite simple, edge groups <p>,<q>,<r> of order 7, face trivial.
# By simplicity every nontrivial hom is vertex-injective; count homs G -> S up to S-conjugacy
# of p (all p-classes, q up to C_S(p)).
Read("girth_lib.g");

FindPair := function(A, g)
  local els7, x, y, tries;
  els7 := Filtered(AsList(A), h -> Order(h) = 7);
  for tries in [1..4000] do
    x := Random(els7); y := Random(els7);
    if not y in Group(x) and Size(Group(x, y)) = Size(A)
       and CosetGraphGirth(A, Group(x), Group(y)) >= g then
      return [x, y];
    fi;
  od;
  return fail;
end;

# Vertex data: relators in two free generators, size, and order filters on short words.
VData := function(A, pair)
  local F, x, y;
  F := Range(IsomorphismFpGroupByGenerators(A, pair));
  x := pair[1]; y := pair[2];
  return rec(rels := RelatorsOfFpGroup(F), fg := FreeGeneratorsOfFpGroup(F), size := Size(A),
             ords := [Order(x*y), Order(x*y^-1), Order(x^2*y), Order(x*y^2), Order(Comm(x, y))],
             girth := CosetGraphGirth(A, Group(x), Group(y)));
end;

OkPair := function(V, u, v)
  local w;
  if Order(u*v) <> V.ords[1] or Order(u*v^-1) <> V.ords[2] or Order(u^2*v) <> V.ords[3]
     or Order(u*v^2) <> V.ords[4] or Order(Comm(u, v)) <> V.ords[5] then return false; fi;
  for w in V.rels do
    if MappedWord(w, V.fg, [u, v]) <> () then return false; fi;
  od;
  return Size(Group(u, v)) = V.size;
end;

SearchS := function(S, VA, VB, VC, e)
  local cl7, cp, p, Cp, qs, c, q, reps, t, r, found, orb;
  cl7 := Filtered(ConjugacyClasses(S), c -> Order(Representative(c)) = 7);
  found := 0;
  for cp in cl7 do
    p := Representative(cp); Cp := Centralizer(S, p);
    qs := [];
    for c in cl7 do for q in c do
      if OkPair(VA, p, q) then Add(qs, q); fi;
    od; od;
    reps := List(Orbits(Cp, qs, OnPoints), o -> o[1]);
    for q in reps do
      t := q^e[1];
      for c in cl7 do for r in c do
        if OkPair(VB, t, r) and OkPair(VC, r^e[2], p^e[3]) then
          found := found + 1;
          if found <= 2 then Print("    hom: |image| = ", Size(Group(p, q, r)), "\n"); fi;
        fi;
      od; od;
    od;
  od;
  return found;
end;

Run := function(label, VA, VB, VC, e, targets)
  local S, t0, n;
  Print(label, " e=", e, " girths=", [VA.girth, VB.girth, VC.girth],
        " sizes=", [VA.size, VB.size, VC.size], "\n");
  for S in targets do
    t0 := Runtime();
    n := SearchS(S, VA, VB, VC, e);
    Print("  |S|=", Size(S), " homs(up to conj)=", n, " ms=", Runtime() - t0, "\n");
  od;
end;
