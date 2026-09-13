# Independent cross-check of the S_n search by Sims' low-index algorithm (GAP
# LowIndexSubgroupsFpGroup) on the finite presentations. A nontrivial action on at most N
# points exists iff there is a subgroup of index 2..N. Calibration first: the literal
# (A7,A7,A7) triple with twisted pairs (e = [3,5,2]) has subgroups of index 7 and 15.
# Driver prepends: NMAXLI := ..;;
Read("tris_lib.g");
Read("cands.g");
A7 := AlternatingGroup(7); A8 := AlternatingGroup(8);
FpTriangle := function(VA, VB, VC, e)
  local F, rels;
  F := FreeGroup("p", "q", "r");
  rels := Concatenation(
    List(VA.rels, w -> MappedWord(w, VA.fg, [F.1, F.2])),
    List(VB.rels, w -> MappedWord(w, VB.fg, [F.2^e[1], F.3])),
    List(VC.rels, w -> MappedWord(w, VC.fg, [F.3^e[2], F.1^e[3]])));
  return F / rels;
end;
Report := function(label, G, N)
  local t0, L;
  t0 := Runtime();
  L := LowIndexSubgroupsFpGroup(G, N);
  Print(label, " N=", N, " subgroups(up to conj)=", Length(L), " indices=",
        Collected(List(L, H -> IndexNC(G, H))), " ms=", Runtime() - t0, "\n");
end;
cal := [ (1,7,4,6,5,2,3), (1,2,4,7,6,3,5), (1,6,3,2,7,4,5) ];
G0 := FpTriangle(MakeVData(A7, [cal[1], cal[2]]), MakeVData(A7, [cal[2]^3, cal[3]]),
                 MakeVData(A7, [cal[3]^5, cal[1]^2]), [3,5,2]);
Report("LI-CAL twisted A7 triple", G0, 15);
for k in [1..4] do
  c := cands[k];
  G := FpTriangle(MakeVData(A7, c.A), MakeVData(A7, c.B), MakeVData(A8, c.C), c.e);
  for N in Filtered([15, 20, 25, 30], x -> x <= NMAXLI) do
    Report(Concatenation("LI-CAND", String(k)), G, N);
  od;
od;
Print("LOWINDEX_DONE\n");
QUIT;
