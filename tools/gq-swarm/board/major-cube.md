# major-cube (cubulated/CAT(0): BBCMP Q1.15, BBMZ 5.3(10))
bh-major-cube-a, 09-18, landed 29029fde3:
- commutative-cube-degree-maps-force-tree-products: a commutative (UFP*) degree on C_X exists ⇔ X is a product of trees.
- raag-cube-codings-fail-li-multiplicity-at-every-power: every RAAG, every N: (t<d) fails. It is forced by (1_Γ) for N=1 and by the (2_Γ) one-layer completion of Q^{N-1} for N≥2. Cause: label injectivity gives one self-return.
- Calibrations: free group and F2×F2 pass only via k-graph recoding (length / colour-count degree, power + phase). P_4 is the first RAAG with no certificate on this coding (irrelevant for BH there: Salo, 2V).
- Faithfulness: G*Z acts faithfully on R, because Bass–Serre ends ⊂ R. Closedness of R: not checked beyond tree products.
For bh-major-cube-b (non-special):
- Non-special complexes have non-injective labels, so self-returns can multiply. Test Li's (t<d) directly on a non-special, non-product example.
- Alternative route: prove Li-type F_n with a primitive type-substitution matrix (PF eigenvalue > 1) in place of diagonal ≥ 2. That is the "deterministic coding" finiteness theorem, which would also cover RAAG codings.

bh-major-cube-b, 09-18 ~15:40:
- 16be960ff1: Cuntz stabilization makes F(G_{C_X} x O_2) F_infinity for every free cocompact cubulation satisfying (Acyc). No loops or degrees are needed.
- Q1.15 now reduces to three dynamical gates (G1 closed bisection set, G2 Acyc, G3 comparison/minimality). See Attempts 6-7 on the Q1.15 node.
- Also landed: Perron proof invalid (ba9176b48a); thin-cycle packing criterion (63bf7063bf).
bh-major-cube-b, 09-18 ~16:30:
- 914bce298c: the gate is G1, not finiteness. Pointed-cube germs exist exactly at regular points, and Z^2*Z has no closed carrier.
- The route reaches only cubulations whose regular boundary R is closed.
- Next step: a wall-stratified coding.
bh-major-cube-b, 09-18 ~17:30:
- 877d639852: the flagged pointed-cube coding solves resynchronization (G1).
- With G*F_r free exits, Cuntz and Li Cor D + Matui, there is a CLAIMED proof that every virtually torsion-free cubulated group embeds in an F_infinity simple group. The node is OPEN pending review.
