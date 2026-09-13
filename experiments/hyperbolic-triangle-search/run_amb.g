# Complete search for homomorphisms of the four (A7,A7,A8) candidates into one finite group S
# given as a permutation group. Driver prepends: TARGET := "<name>";; CANDS := [..];;
# Calibration built in: a literal (A8,A8,A8) triple inside A8 maps into every S containing A8,
# so SearchAmb must report at least one hom for it before the candidate zeros are recorded.
Read("tris_lib.g");
Read("cands.g");
A7 := AlternatingGroup(7); A8 := AlternatingGroup(8);
PermOf := function(G)
  local iso;
  iso := IsomorphismPermGroup(G);
  return Image(SmallerDegreePermutationRepresentation(Image(iso)));
end;
MakeTarget := function(name)
  if name = "Sp6_2" then return PermOf(Sp(6,2));
  elif name = "L5_2" then return PermOf(SL(5,2));
  elif name = "L6_2" then return PermOf(SL(6,2));
  elif name = "L4_4" then return PSL(4,4);
  elif name = "O8p2" then return PermOf(Omega(1,8,2));
  elif name = "O8m2" then return PermOf(Omega(-1,8,2));
  elif name = "Sp8_2" then return PermOf(Sp(8,2));
  elif name = "O7_3" then return PermOf(Omega(7,3));
  elif name = "U6_2" then return PSU(6,2);
  elif name = "L4_8" then return PSL(4,8);
  fi;
  Error("unknown target");
end;
t0 := Runtime();
S := MakeTarget(TARGET);
Print("TARGET ", TARGET, " |S|=", Size(S), " degree=", NrMovedPoints(S),
      " classes=", NrConjugacyClasses(S), " ms=", Runtime() - t0, "\n");
# Calibration triple (same seed as cal1.g).
rs := RandomSource(IsMersenneTwister, 20260913);
els := Filtered(AsList(A8), g -> Order(g) = 7);
repeat
  tr := List([1..3], i -> Random(rs, els));
until Size(Group(tr[1], tr[2])) = 20160 and Size(Group(tr[2], tr[3])) = 20160
      and Size(Group(tr[3], tr[1])) = 20160;
WA := MakeVData(A8, [tr[1], tr[2]]); WB := MakeVData(A8, [tr[2], tr[3]]);
WC := MakeVData(A8, [tr[3], tr[1]]);
t0 := Runtime();
res := SearchAmb(WA, WB, WC, [1,1,1], S);
Print("CAL ", TARGET, " literal (A8,A8,A8): stats=", res.stats, " homs=", Length(res.found),
      " ms=", Runtime() - t0, "\n");
if Length(res.found) = 0 then Print("CALIBRATION FAILED\n"); fi;
for k in CANDS do
  c := cands[k];
  VA := MakeVData(A7, c.A); VB := MakeVData(A7, c.B); VC := MakeVData(A8, c.C);
  t0 := Runtime();
  res := SearchAmb(VA, VB, VC, c.e, S);
  Print("CAND", k, " ", TARGET, " stats=", res.stats, " homs=", Length(res.found),
        " ms=", Runtime() - t0, "\n");
od;
Print("RUN_AMB_DONE\n");
QUIT;
