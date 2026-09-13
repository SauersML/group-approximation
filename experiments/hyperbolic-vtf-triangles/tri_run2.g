Read("tri_search.g");
A7 := AlternatingGroup(7); A8 := AlternatingGroup(8);
# The four hyperbolic (A7,A7,A8) Z/7-triangles of run 1 (type (3,3,4)), hardcoded.
cands := [
  rec(A := [(1,4,6,3,5,7,2), (1,4,6,3,7,2,5)], B := [(1,6,4,7,2,5,3), (1,5,4,7,3,2,6)],
      C := [(2,6,5,8,3,7,4), (1,2,7,4,3,6,8)], e := [4,2,4]),
  rec(A := [(1,5,3,2,7,4,6), (1,7,4,2,3,6,5)], B := [(1,3,4,7,5,2,6), (1,7,4,5,6,3,2)],
      C := [(2,6,3,7,4,5,8), (1,4,3,5,7,8,6)], e := [1,3,3]),
  rec(A := [(1,3,6,7,4,5,2), (1,6,5,3,4,7,2)], B := [(1,7,6,4,2,5,3), (1,3,4,2,6,5,7)],
      C := [(1,8,4,7,3,5,2), (1,4,6,2,3,8,7)], e := [4,3,3]),
  rec(A := [(1,6,7,4,5,2,3), (1,5,6,3,4,2,7)], B := [(1,3,2,7,4,6,5), (1,2,7,5,4,3,6)],
      C := [(1,8,4,3,6,5,2), (1,8,6,4,2,7,3)], e := [3,3,6]) ];
Sp62 := Image(IsomorphismPermGroup(Sp(6,2)));
targets := [Sp62, AlternatingGroup(11), AlternatingGroup(12), AlternatingGroup(13)];
for k in [1..Length(cands)] do
  c := cands[k];
  Run(Concatenation("CAND", String(k), " (A7,A7,A8) (3,3,4) run2"),
      VData(A7, c.A), VData(A7, c.B), VData(A8, c.C), c.e, targets);
od;
Print("DONE\n");
QUIT;
