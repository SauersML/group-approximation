---
rg: 2
id: simple-cstar-unitary-components-class-five
kind: claim
title: Some simple unital C*-algebra has a unitary component group with a nonzero fivefold commutator
distinct_from:
  simple-cstar-unitary-components-class-four: That asks for a nonzero fourfold commutator and is answered by lambda-mod-8 trapping of eta cubed; this asks for depth four, where every rank-two bordism detector is blind.
  simple-cstar-unitary-component-group-not-nilpotent: That asks for nonzero commutators of every depth in one algebra; this asks only for depth four.
---

**OPEN.** Find a simple unital C*-algebra A and unitaries u_1, ..., u_4, v in
A with [u_4, [u_3, [u_2, [u_1, v]]]] not in U_0(A).

Any AH example needs blocks of excess at least three cofinally
(block-component-group-class-at-most-excess-plus-two). The witness has
finite order and dies in some M_n(A)
(ah-unitary-component-kernel-is-locally-finite).

## Attempts

- *Rank-two protected block, any seed, any bordism detector.* Dead for
  witnesses (f o pr_M) (+) 1_Q. The stable fivefold commutator map of U(2) is
  null (rank-two-trapping-blind-to-depth-four-brackets), so every trapped
  homology class vanishes: Spin, lambda-mod-8, String or framed.
- *Rank-three protected block C^3.* Live, unexplored. Here W = 3·Q*, so
  dim X = 6r and the Euler number is <c_r(Q)^3, [X]>. The letters of the
  stable commutator of U(3) are maps between cells of
  Sigma^∞ SU(3) = S^3 ∪ e^5 ∪ e^8, not elements of pi_*^s. The degree-zero
  letters vanish, because the Pontryagin ring H_*(SU(3)) is exterior on
  primitives. The attaching maps can still carry products through Toda
  brackets. The alpha-brackets <alpha, <alpha, a_3>> die by bilinearity
  (simple-cstar-unitary-components-class-four, Attempts).
- *Witnesses that mix the protected block with Q.* Unexplored. The trapped
  invariant is only constant on components, not a homomorphism. A commutator
  with a unitary that is not block diagonal is not computed by the seed
  formula.
- *Unstable detectors.* None known. The unstable map cbar_5 of U(2) may be
  essential at a finite stage. Its survival in a simple limit would need an
  invariant of sections that is not a homology class of the block-diagonal
  locus.
