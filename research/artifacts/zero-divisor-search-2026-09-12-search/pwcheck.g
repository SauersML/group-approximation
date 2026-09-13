# Independent GAP check of the n = 22 power-sieve exclusions. For each excluded leaf: Q = <x, y | cycle
# words, roots u of the power relations u^e = 1 found by zds>; if Q is finite, count distinct edge products.
F := FreeGroup("x", "y");;
ZdsWord := function(s)
  local w, c;
  w := One(F);
  for c in s do
    if c = 'x' then w := w * F.1;
    elif c = 'X' then w := w * F.1^-1;
    elif c = 'y' then w := w * F.2;
    elif c = 'Y' then w := w * F.2^-1; fi;
  od;
  return w;
end;;
Read("pwprune.g");;
Print("excluded leaves: ", Length(ZdsPw), "\n");
for i in [1..Length(ZdsPw)] do
  item := ZdsPw[i];;
  cyc := List(item[1], ZdsWord);; pw := List(item[2], p -> ZdsWord(p[1]));; edges := List(item[3], ZdsWord);;
  rels := Concatenation(cyc, pw);;
  Print("== leaf ", i, ": ", Length(cyc), " cycle relators, ", Length(pw), " power roots, exponents ", List(item[2], p -> p[2]), "\n");
  ct := CosetTableFromGensAndRels(GeneratorsOfGroup(F), rels, [] : max := 4000000, silent := true);;
  if ct = fail then
    Print("  Q: enumeration exceeds 4000000 cosets\n");
  else
    px := PermList(ct[1]);; py := PermList(ct[3]);;
    pts := List(edges, w -> 1 ^ MappedWord(w, GeneratorsOfGroup(F), [px, py]));;
    Print("  Q: order ", Length(ct[1]), ", distinct edge products ", Length(Set(pts)), " of ", Length(edges), "\n");
  fi;
od;
Print("GAPDONE\n");
QUIT;
