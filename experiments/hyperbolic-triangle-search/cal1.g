# Calibration of tris_lib.g.
# (C1) literal (A7,A7,A7) triple from ex-hyperbolic-vtf, e=[1,1,1]: per-alpha beta counts from
#      the double-coset search must equal a naive scan over all 7-cycles of S_n, n = 7..10.
# (C2) the same triple must map into S_15, S_21, S_22 (A7 acting on 15, 21, 7+15 points), and
#      |Hom(G,S_15)| from SearchSn must equal the count from SearchAmb (AllHomomorphismClasses).
# (C3) a literal (A8,A8,A8) triple must map into S_15, S_16 and S_28.
Read("tris_lib.g");
A7 := AlternatingGroup(7); A8 := AlternatingGroup(8);
cal := [ (1,7,4,6,5,2,3), (1,2,4,7,6,3,5), (1,6,3,2,7,4,5) ];
VA := MakeVData(A7, [cal[1], cal[2]]); VB := MakeVData(A7, [cal[2], cal[3]]);
VC := MakeVData(A7, [cal[3], cal[1]]); e := [1,1,1];
TA := TransitiveTypes(VA, 30); TB := TransitiveTypes(VB, 30);
Print("A7 transitive degrees <= 30: ", List(TA, t -> t.deg), "\n");
for n in [7..10] do
  t0 := Runtime();
  res := SearchSn(VA, VB, VC, e, n, TA, TB);
  for a in res.alphas do
    nv := NaiveBetaCount(VB, VC, e, n, a, 7);
    Print("C1 n=", n, " alpha=", a.combo, " cls=", a.cls, " dc-count=", a.nbeta, " naive=", nv,
          " ", String(a.nbeta = nv), "\n");
  od;
  Print("C1 n=", n, " stats=", res.stats, " |Hom|=", TotalHoms(SymmetricGroup(n), res),
        " ms=", Runtime() - t0, "\n");
od;
for n in [15, 21, 22] do
  t0 := Runtime();
  res := SearchSn(VA, VB, VC, e, n, TA, TB);
  Print("C2 n=", n, " stats=", res.stats, " transitive-found=",
        Number(res.found, f -> f.orbits = [n]), " ms=", Runtime() - t0, "\n");
  # (the S_15 SearchAmb cross-check ran over 12 minutes in AllHomomorphismClasses and was
  #  moved to cal2.g at n = 11)
od;
# (C3) literal (A8,A8,A8) triple, deterministic random choice.
rs := RandomSource(IsMersenneTwister, 20260913);
els := Filtered(AsList(A8), g -> Order(g) = 7);
repeat
  tr := List([1..3], i -> Random(rs, els));
until Size(Group(tr[1], tr[2])) = 20160 and Size(Group(tr[2], tr[3])) = 20160
      and Size(Group(tr[3], tr[1])) = 20160;
Print("C3 triple ", tr, "\n");
WA := MakeVData(A8, [tr[1], tr[2]]); WB := MakeVData(A8, [tr[2], tr[3]]);
WC := MakeVData(A8, [tr[3], tr[1]]);
UA := TransitiveTypes(WA, 30); UB := TransitiveTypes(WB, 30);
Print("A8 transitive degrees <= 30: ", List(UA, t -> t.deg), "\n");
for n in [15, 16, 28] do
  t0 := Runtime();
  res := SearchSn(WA, WB, WC, [1,1,1], n, UA, UB);
  Print("C3 n=", n, " stats=", res.stats, " transitive-found=",
        Number(res.found, f -> f.orbits = [n]), " ms=", Runtime() - t0, "\n");
od;
Print("CAL1_DONE\n");
QUIT;
