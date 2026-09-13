# Calibration of the exponent path of tris_lib.g. The literal (A7,A7,A7) triple (p,q,r) with
# twisted vertex pairs A=(p,q), B=(q^3,r), C=(r^5,p^2) defines G_e with e = [3,5,2] for which
# p,q,r -> the literal permutations is a hom. SearchSn must find transitive homs of degree
# 7 and 15 (A7 on 7 and 15 points) and SearchAmb must find homs into L5_2 (A7 < A8 = L4(2) < L5(2)).
# The untwisted-pair run with the same e is recorded for comparison (no forced answer).
Read("tris_lib.g");
A7 := AlternatingGroup(7);
cal := [ (1,7,4,6,5,2,3), (1,2,4,7,6,3,5), (1,6,3,2,7,4,5) ];
e := [3,5,2];
VA := MakeVData(A7, [cal[1], cal[2]]); VB := MakeVData(A7, [cal[2]^3, cal[3]]);
VC := MakeVData(A7, [cal[3]^5, cal[1]^2]);
TA := TransitiveTypes(VA, 22); TB := TransitiveTypes(VB, 22);
for n in [7, 15, 22] do
  t0 := Runtime();
  res := SearchSn(VA, VB, VC, e, n, TA, TB);
  Print("CAL2 twisted n=", n, " homs=", Length(res.found), " transitive=",
        Number(res.found, f -> f.orbits = [n]), " |Hom|=", TotalHoms(SymmetricGroup(n), res),
        " ms=", Runtime() - t0, "\n");
od;
S := Image(SmallerDegreePermutationRepresentation(Image(IsomorphismPermGroup(SL(5,2)))));
res := SearchAmb(VA, VB, VC, e, S);
Print("CAL2 twisted L5_2 homs=", Length(res.found), " |Hom|=", TotalHoms(S, res), "\n");
# Cross-check of total counts between the two complete methods at n = 11.
res1 := SearchSn(VA, VB, VC, e, 11, TA, TB);
res2 := SearchAmb(VA, VB, VC, e, SymmetricGroup(11));
Print("CAL2 |Hom(G,S11)| SearchSn=", TotalHoms(SymmetricGroup(11), res1), " SearchAmb=",
      TotalHoms(SymmetricGroup(11), res2), "\n");
Print("CAL2_DONE\n");
QUIT;
