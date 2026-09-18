# Output: k1222_cert.out, k1222_p3_monomial.json.  K_{1,2,2,2}, p=3: reduce the class-3
# 3-quotient to cyclic centre <J>, re-verify relators, build exact monomial representation.
OnBreak := function() FORCE_QUIT_GAP(3); end;
Read("monomial_fast.g");
part := [1,2,2,3,3,4,4];
k1222 := Filtered(Combinations([1..7], 2), e -> part[e[1]] <> part[e[2]]);
Print("edges ", k1222, "\n");
R := ReduceAndVerify("K1222", 7, k1222, 3, 3);
MonomialCertFast(R, 3, "k1222_p3_monomial.json");
QUIT;
