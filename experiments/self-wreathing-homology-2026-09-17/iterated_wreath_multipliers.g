# Calibration for self-wreathing-groups-are-not-fp-infinity.
# W_1 = P, W_{n+1} = W_n wr_X P (GAP's WreathProduct(W_n, P): |X| copies of W_n permuted by P).
# The node predicts: H_1(W_n) = (P^ab)^n, and for perfect P, H_2(W_n) = H_2(P)^n.
# It also prints the Schur multipliers H_2(P) of the root images used in the node.
Iter := function(P, n)
  local W, i;
  W := P;
  for i in [2..n] do W := WreathProduct(W, P); od;
  return W;
end;
Report := function(name, P, nmax, doMult)
  local n, W;
  for n in [1..nmax] do
    W := Iter(P, n);
    Print(name, "  n=", n, "  degree=", NrMovedPoints(W), "  |W_n|=", Size(W),
          "  H_1=", AbelianInvariants(W));
    if doMult then Print("  H_2=", AbelianInvariantsMultiplier(W)); fi;
    Print("\n");
  od;
end;
Report("Z/3 on 3 pts", AlternatingGroup(3), 4, false);
Report("A_4 on 4 pts", AlternatingGroup(4), 3, false);
# GAP's multiplier routine exhausts its coset table on A_5 wr A_5 (order 60^6); the level-2 lower bound
# for H_2 is certified instead by explicit_central_extension.g.
Report("A_5 on 5 pts", AlternatingGroup(5), 1, true);
Report("A_6 on 6 pts", AlternatingGroup(6), 1, true);
Report("A_7 on 7 pts", AlternatingGroup(7), 1, true);
Report("A_8 on 8 pts", AlternatingGroup(8), 1, true);
Print("A_5 wr A_5: H_1=", AbelianInvariants(WreathProduct(AlternatingGroup(5), AlternatingGroup(5))), "\n");
Print("M_11 on 11 pts: perfect=", IsPerfectGroup(MathieuGroup(11)),
      "  H_2=", AbelianInvariantsMultiplier(MathieuGroup(11)), "\n");
# M_23 (trivial multiplier, cited) is not computed: the multiplier routine exceeds the 1200s limit.
QUIT;
