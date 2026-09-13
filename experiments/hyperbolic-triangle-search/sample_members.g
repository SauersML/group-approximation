# sample_members.g -- random members of the family F: (A7,A7,A8) triangles with Z/7 edges,
# link girths (6,6,8), random twists. Writes members.py (python list of dicts, GAP perm strings),
# the same format as cands.py. Driver prepends: NSAMP := ..;; SEED := ..;;
Read("girth_lib.g");
A7 := AlternatingGroup(7); A8 := AlternatingGroup(8);
rs := RandomSource(IsMersenneTwister, SEED);
E7 := Filtered(AsList(A7), g -> Order(g) = 7); E8 := Filtered(AsList(A8), g -> Order(g) = 7);
RandPair := function(G, els, sz, g)
  local x, y;
  repeat
    x := Random(rs, els); y := Random(rs, els);
  until Size(Group(x, y)) = sz and CosetGraphGirth(G, Group(x), Group(y)) = g;
  return [x, y];
end;
PS := p -> ReplacedString(String(p), " ", "");
out := OutputTextFile("members.py", false); SetPrintFormattingStatus(out, false);
AppendTo(out, "CANDS = [\n");
for i in [1..NSAMP] do
  pa := RandPair(A7, E7, 2520, 6); pb := RandPair(A7, E7, 2520, 6); pc := RandPair(A8, E8, 20160, 8);
  e := List([1..3], j -> Random(rs, [1..6]));
  AppendTo(out, "  {\"A\": [\"", PS(pa[1]), "\", \"", PS(pa[2]), "\"], \"B\": [\"", PS(pb[1]), "\", \"",
           PS(pb[2]), "\"], \"C\": [\"", PS(pc[1]), "\", \"", PS(pc[2]), "\"], \"e\": [", e[1], ", ",
           e[2], ", ", e[3], "]},\n");
od;
AppendTo(out, "]\n"); CloseStream(out);
Print("SAMPLE_DONE ", NSAMP, "\n");
QUIT;
