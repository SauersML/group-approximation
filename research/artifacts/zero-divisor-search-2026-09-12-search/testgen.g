# Soundness test data for zds.c: labelled Kaplansky structures realized in finite groups.
# For a finite group G and x, y in G with 1, x, y distinct, every nonzero beta in F_2[G] with
# (1 + x + y) beta = 0 gives a cubic Kaplansky multigraph on supp beta: each product s = a b
# (a in {1,x,y}, b in supp beta) has exactly one other expression a' b'.  Each connected component
# is written as "n m u v p q ..." (ports 0 = 1, 1 = x, 2 = y), with n <= 40.
# Output file: testdata.txt.  Core GAP; small groups from the SmallGroups library when available.

ZdsOut := OutputTextFile("testdata.txt", false);;
SetPrintFormattingStatus(ZdsOut, false);;
ZdsCount := 0;;

ZdsEmit := function(G, els, x, y, supp)
  local ports, B, pos, seen, comp, stack, b, i, a, s, j, bb, edges, key, done, u, v;
  ports := [ One(G), x, y ];
  B := List(supp, i -> els[i]);
  seen := [];
  for b in [1..Length(B)] do
    if b in seen then continue; fi;
    comp := [ b ]; AddSet(seen, b); stack := [ b ];
    while Length(stack) > 0 do
      u := Remove(stack);
      for i in [1..3] do
        s := ports[i] * B[u];
        for j in [1..3] do
          if j = i then continue; fi;
          pos := Position(B, ports[j]^-1 * s);
          if pos <> fail and not pos in seen then AddSet(seen, pos); Add(comp, pos); Add(stack, pos); fi;
        od;
      od;
    od;
    if Length(comp) > 40 then continue; fi;
    edges := []; done := [];
    for u in [1..Length(comp)] do
      for i in [1..3] do
        s := ports[i] * B[comp[u]];
        for j in [1..3] do
          if j = i then continue; fi;
          pos := Position(B, ports[j]^-1 * s);
          if pos = fail then continue; fi;
          v := Position(comp, pos);
          key := Set([ [u, i], [v, j] ]);
          if not key in done then AddSet(done, key); Add(edges, [u - 1, v - 1, i - 1, j - 1]); fi;
        od;
      od;
    od;
    if Length(edges) <> 3 * Length(comp) / 2 then Print("edge count mismatch\n"); continue; fi;
    PrintTo(ZdsOut, Length(comp), " ", Length(edges));
    for key in edges do PrintTo(ZdsOut, " ", key[1], " ", key[2], " ", key[3], " ", key[4]); od;
    PrintTo(ZdsOut, "\n");
    ZdsCount := ZdsCount + 1;
  od;
end;;

ZdsGroup := function(G, maxpairs)
  local els, N, x, y, M, i, b, a, ns, d, k, v, pairs, supps, supp, p;
  els := AsSSortedList(G); N := Length(els);
  pairs := [];
  for x in els do for y in els do
    if x <> One(G) and y <> One(G) and x <> y then Add(pairs, [x, y]); fi;
  od; od;
  if Length(pairs) > maxpairs then pairs := List([1..maxpairs], i -> Random(pairs)); fi;
  for p in pairs do
    x := p[1]; y := p[2];
    M := NullMat(N, N, GF(2));
    for b in [1..N] do
      for a in [ One(G), x, y ] do
        i := Position(els, a * els[b]);
        M[b][i] := M[b][i] + One(GF(2));
      od;
    od;
    ns := NullspaceMat(M); d := Length(ns);
    if d = 0 then continue; fi;
    supps := [];
    if d <= 6 then
      for k in [1..2^d - 1] do
        v := Sum([1..d], i -> (QuoInt(k, 2^(i - 1)) mod 2) * ns[i]);
        AddSet(supps, Filtered([1..N], i -> not IsZero(v[i])));
      od;
    else
      for k in [1..64] do
        v := Sum([1..d], i -> Random([0, 1]) * ns[i]);
        if not IsZero(v) then AddSet(supps, Filtered([1..N], i -> not IsZero(v[i]))); fi;
      od;
    fi;
    for supp in supps do ZdsEmit(G, els, x, y, supp); od;
  od;
end;;

Print("smallgrp: ", TestPackageAvailability("smallgrp"), "\n");
ZdsGroups := [];;
if TestPackageAvailability("smallgrp") <> fail then
  LoadPackage("smallgrp");
  for k in [6..40] do Append(ZdsGroups, AllSmallGroups(k)); od;
else
  for k in [3..20] do Add(ZdsGroups, DihedralGroup(2 * k)); Add(ZdsGroups, CyclicGroup(IsPermGroup, 2 * k)); od;
  for k in [2..5] do Add(ZdsGroups, QuaternionGroup(2^(k + 1))); od;
  Add(ZdsGroups, SymmetricGroup(4)); Add(ZdsGroups, AlternatingGroup(5));
fi;
Print("groups: ", Length(ZdsGroups), "\n");
for G in ZdsGroups do ZdsGroup(G, 40); od;
# a few larger non-abelian groups with sampled pairs
for G in [ AlternatingGroup(5), SL(2, 5), PSL(2, 7), SymmetricGroup(5) ] do ZdsGroup(G, 15); od;
CloseStream(ZdsOut);
Print("structures: ", ZdsCount, "\nGAPDONE\n");
QUIT;
