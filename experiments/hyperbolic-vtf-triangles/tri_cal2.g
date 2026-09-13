Read("tri_search.g");
A7 := AlternatingGroup(7);
# Literal Euclidean (A7,A7,A7) triple from run 1; its inclusion A7 < A_n is a hom into every A_n,
# so SearchS must report found >= 1 for S = A9, A10, A11 (tests the larger-S code path).
cal := [ (1,7,4,6,5,2,3), (1,2,4,7,6,3,5), (1,6,3,2,7,4,5) ];
Run("CALIBRATION2 literal (A7,A7,A7) into larger S",
    VData(A7, [cal[1], cal[2]]), VData(A7, [cal[2], cal[3]]), VData(A7, [cal[3], cal[1]]),
    [1, 1, 1], [AlternatingGroup(9), AlternatingGroup(10), AlternatingGroup(11)]);
Print("DONE\n");
QUIT;
