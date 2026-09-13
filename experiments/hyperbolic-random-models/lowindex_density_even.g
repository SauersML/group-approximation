# Calibration: small-index quotients of density-model random groups on 2 generators.
# For each relator length len and density d (percent), sample 8 presentations with
# Int(3^(d*len/100)) freely reduced random relators of length len, and report how many
# have no proper subgroup of index <= 5 and how many are perfect.
SetInfoLevel(InfoWarning, 0);
rs := RandomSource(IsMersenneTwister, 20260912);
F := FreeGroup(2);
letters := Concatenation(GeneratorsOfGroup(F), List(GeneratorsOfGroup(F), g -> g^-1));
RandRedWord := function(len)
  local w, prev, x, i;
  w := One(F); prev := fail;
  for i in [1..len] do
    repeat
      x := letters[Random(rs, 1, 4)];
    until prev = fail or x <> prev^-1;
    w := w * x; prev := x;
  od;
  return w;
end;
for len in [8, 10, 12] do
  for d in [20, 25, 30, 35, 40, 45] do
    nrel := Int(Float(3)^(Float(d * len) / 100));
    noproper := 0; perfect := 0;
    for s in [1..8] do
      rels := List([1..nrel], i -> RandRedWord(len));
      G := F / rels;
      L := LowIndexSubgroupsFpGroup(G, 5);
      if Length(L) = 1 then noproper := noproper + 1; fi;
      if AbelianInvariants(G) = [] then perfect := perfect + 1; fi;
    od;
    Print("len=", len, " d=0.", d, " relators=", nrel, " no_proper_index<=5=", noproper, "/8 perfect=", perfect, "/8\n");
  od;
od;
QUIT;
