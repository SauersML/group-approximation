# bh-free-28 (free lane)
**Direction (09-18):** the free centre-by-metabelian groups C_r = F_r/[F_r'',F_r] (main node `free-centre-by-metabelian-groups-satisfy-boone-higman`, OPEN; bh-testcases' hard case "C_2"). Plan: a second-order Magnus embedding (4x4 unitriangular-type matrices over Z[x^±,y^±]) proving C_2 linear, hence in B_A via the char-0 linear node; then the reduction "C_r linear iff residually finite" for r >= 4 via Gupta 1973.
**Landed (09-18):** c20193cd0 (C_2 linear via explicit 4x4 rep; C_2 in B_A; r>=4 linear iff RF via Gupta 1973 abstract), 386fd7a93 (parent node status + Attempt 5), e732575e5 + 93c623957 (rank-n: C_n/K_n linear via n^2 3x3 reps; K_n f.g. of rank <= C(n,3)+C(n,4); K_3 cyclic). Open: K_3 = 0? (one H_3(Z^3)-class; a Hall–Witt identity may kill it), RF of C_r for r >= 4.
**Landed (09-18 10:15): a5552e32f.** SETTLED: every free centre-by-metabelian group C_n is linear in char 0, hence in B_A. The parent node free-centre-by-metabelian-groups-satisfy-boone-higman is now ESTABLISHED through free-centre-by-metabelian-bh-via-linearity.
- (2n+1) corner rep kernel = torsion T_n; K_3 = 0 (so C_3 ↪ GL_7(Z[x^±,y^±,z^±])); T_n = (Z/d)^C(n,4) with retraction coordinates.
- Gupta–Levin 1986 Lemma 4.4 gives u_6 ∉ γ_7, so C_n ↪ ρ_n(C_n) × C_n/γ_7(C_n).
- C_n is also residually nilpotent. Priority correction (bh-verify-cbm, 91129a0bc): linearity of all C_n is Gupta–Wehrfritz 1976, Remark 3, so this chain is a new proof of a known theorem. The false cyclic-subgroup step was repaired in ec2c676a9.
Lane proofs, not independently reviewed.
**bh-verify-cbm (09-18, ec2c676a9): PASS with one repair.**
- **Checked and PASS:** K_n = T_n, K_3 = 0, and Gupta–Levin Lemmas 2.2 and 4.4, read at source.
- **False lemma:** route step 3 says "every nontrivial subgroup of a cyclic group of even order contains the involution". That's false (Z/3 ≤ Z/6). The step holds given Kuz'min's d = 2.
- **Kuz'min-free repair:** ∩γ_c ⊆ ker θ has exponent 2 (Lemma 2.2), so T_4 ∩ ∩γ_c = 1. That gives linearity via γ_c for some finite c. It's recorded as an Attempts note on the route node.
- **Small miscount:** u_6 has 8 weight-7 factors, not 6.
- **Priority open:** N. D. Gupta–Wehrfritz, Arch. Math. 27 (1976), and C. K. Gupta–Levin, Comm. Algebra 4 (1976), were unreadable (403). Check them on MathSciNet before claiming anything new for n ≥ 4.
**bh-verify-cbm priority update (91129a0bc):** KNOWN THEOREM. N. D. Gupta–Wehrfritz, Arch. Math. 27 (1976), p. 454, Remark 3, proves every free centre-by-metabelian group of finite rank linear; I read it at source via MSI. Facts (ii) and (iii), credited to C. K. Gupta, give torsion (Z/2)^C(r,4) and residually finite 2-group. So the lane chain is a new explicit proof, not a new result. The node's priority line is updated.
