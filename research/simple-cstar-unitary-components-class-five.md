---
rg: 2
id: simple-cstar-unitary-components-class-five
kind: claim
title: Some simple unital C*-algebra has a unitary component group with a nonzero fivefold commutator
distinct_from:
  simple-cstar-unitary-components-class-four: That asks for a nonzero fourfold commutator and is answered by lambda-mod-8 trapping of eta cubed; this asks for depth four, where every rank-two bordism detector is blind.
  simple-cstar-unitary-component-group-not-nilpotent: That asks for nonzero commutators of every depth in one algebra; this asks only for depth four.
artifacts:
  - research/artifacts/class-four-lambda-mod-eight-trapping-part3-2026-09-13.md
  - research/artifacts/class-four-lambda-mod-eight-trapping-part4-2026-09-13.md
---

**OPEN.** Find a simple unital C*-algebra A and unitaries u_1, ..., u_4, v in
A with [u_4, [u_3, [u_2, [u_1, v]]]] not in U_0(A).

Any AH example needs blocks of excess at least three cofinally
(block-component-group-class-at-most-excess-plus-two). The witness has
finite order and dies in some M_n(A)
(ah-unitary-component-kernel-is-locally-finite).

A finite-stage input suffices. Suppose some closed Spin_m-manifold M and some
unitaries in C(M, M_p) have a fivefold commutator whose reduced
Spin_m-bordism class in U(p) is nonzero. Then the transfer theorem
(unitary-word-transfer-to-simple-ah-via-trapping) gives a simple unital AH
algebra with a nonzero fivefold commutator.

## Attempts

- *Rank-two protected block, any seed, any bordism detector.* Dead for
  witnesses (f o pr_M) (+) 1_Q. The stable fivefold commutator map of U(2) is
  null (rank-two-trapping-blind-to-depth-four-brackets), so every trapped
  homology class vanishes: Spin, lambda-mod-8, String or framed. The
  sphere-product special case follows from the vanishing of every
  eta^a·y^b with a + b = 4
  (rank-two-trapping-blind-to-fivefold-sphere-commutators).
- *Rank-three protected block C^3.* Live, unexplored. Here W = 3·Q*, so
  dim X = 6r and the Euler number is <c_r(Q)^3, [X]>. Steps
  Gr_m(H^{m+3d}) exist, with defect m·q_1 and count ±1 (transfer theorem). The
  letters of the stable commutator of U(3) are maps between cells of
  Sigma^∞ SU(3) = S^3 ∪ e^5 ∪ e^8, not elements of pi_*^s. The degree-zero
  letters vanish, because the Pontryagin ring H_*(SU(3)) is exterior on
  primitives. The attaching maps can still carry products through Toda
  brackets. The alpha-brackets <alpha, <alpha, a_3>> die by bilinearity
  (simple-cstar-unitary-components-class-four, Attempts). For odd p the
  evaluation U(p) -> S^{2p−1} is zero on pi_{2p} U(p), so stem-one readings
  of Bott brackets die there.
- *Spin detection in any rank.* For every N, KO- and Stiefel–Whitney numbers
  with reduced coefficients vanish on fourfold commutators
  (nested-commutators-pull-ko-of-unitary-groups-into-eta-powers). Spin
  bordism itself is blind on fourfold commutators in every rank, because
  MSpin_(2) splits into ko-modules
  (spin-trapping-blind-to-fourfold-commutators-in-every-rank). So a fivefold
  input needs a structure whose bordism is not a sum of ko-modules, such as
  lambda mod m.
- *Spin_m detection, m >= 2.* Open. The relative lambda-mod-m e-invariant
  reaches eta^3 at depth three. Depth four would need a length-four torsion
  product visible in Omega^{Spin_m}_*, or classes carried by higher cells of
  U(p).
- *String or tmf detection.* That would see nu^2 and products involving
  kappa-bar, but it needs lambda(TX − W_R) = 0 exactly. Quaternionic steps
  have defect k·q_1 with k >= 1, and complex Grassmannians carry a c_1^2
  term. No step family with defect zero and odd Euler count is known.
  Quaternionic partial flag manifolds with tautological Q never give one,
  whatever the protected rank
  (quaternionic-flag-trapping-steps-are-never-string).
- *Odd primes are exhausted in small rank.* The witness has finite order, so
  its class splits into p-primary parts. So, arXiv:1707.00739v2, p. 1:
  "Kaji and Kishimoto [3] showed that p-regular Lie groups have homotopy
  nilpotence class at most 3. When G is quasi-p-regular and p ≥ 7, Kishimoto
  [4] showed that SU(n) has homotopy nilpotence class at most 3". There class
  n means that the n-fold iterated commutator c_n (on n + 1 inputs) is null.
  SU(k) is p-regular for p >= k. So for SU(k)-valued seeds every depth-three
  bracket (c_3), and hence every depth-four bracket (c_4), is trivial at all
  primes p >= k. For k = 3 a class-five seed must be 2-primary. For k = 4 it
  must be 2- or 3-primary. For U(k)-valued seeds this holds at primes not
  dividing k; the primes dividing k were not checked.
- *Witnesses that mix the protected block with Q.* Unexplored. The trapped
  invariant is only constant on components, not a homomorphism. A commutator
  with a unitary that is not block diagonal is not computed by the seed
  formula.
- *Unstable detectors.* None known. The unstable map cbar_5 of U(2) may be
  essential at a finite stage. Its survival in a simple limit would need an
  invariant of sections that is not a homology class of the block-diagonal
  locus.
