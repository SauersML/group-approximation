---
rg: 2
id: toms-trapped-spin-bordism-class-citation
kind: route
title: Import Theorem 3.3, Proposition 4.2, Lemma 5.1, Proposition 5.2, Lemma 6.3 and Lemma 7.1 of Toms arXiv:2609.09535v1
target: toms-trapped-spin-bordism-class
requires: []
artifacts:
  - research/artifacts/class-three-spin-bordism-trapping-2026-09-12.md
  - research/artifacts/toms-lix-k1-injectivity-import-2026-09-12.md
---

Source: A. S. Toms, "A simple C*-algebra which is not K1-injective",
arXiv:2609.09535v1, 24 pages. The lane `ex-unitary-class-three` read all 24
pages of the PDF on 2026-09-12. The paper is unrefereed.

Verbatim, from the cited pages:

- Theorem 3.3 (p. 11): "The class nu_{X,Q}(v) is independent of the chosen
  transverse representative and depends only on the path component of v in
  U(Gamma(End E))."
- Proposition 4.2 (p. 14): "Let X, Q, B, E be as in section 3, let
  u: S^4 -> SU(2) represent the nonzero element of pi_4(SU(2)), and put
  w = (u o pr_{S^4}) (+) 1_Q. Then nu_{X,Q}(1_E) = 0,
  nu_{X,Q}(w) = <e(W_R), [X]> eta_Spin = <c_r(Q)^2, [X]> eta_Spin."
- Lemma 5.1(iii) (p. 16): "<c_2(zeta_d)^{2d}, [G(d)]> = 1" for
  G(d) = Gr_2(C^{2d+2}), which is simply connected and spin.
- Proposition 5.2 (pp. 17-18): with d_i = m_i N_i and X_{i+1} = X_i x G(d_i),
  (30) "dim_R X_{i+1} = 4 r_{i+1}" and
  (31) "<c_{r_{i+1}}(Q_{i+1})^2, [X_{i+1}]> = 1".
- Lemma 6.3 (p. 20): an injective unital inductive system in which every
  nonzero positive element becomes full at a later stage has a simple limit.
- Lemma 7.1 (p. 21): "If the image of v in B belongs to U_0(B), then there
  is j >= i such that psi_{i,j}(v) in U_0(B_j)."

The setting of Section 3 (p. 9) is "Let X be a closed, connected, simply
connected smooth spin manifold of real dimension 4r, and let Q -> X be a
Hermitian complex vector bundle of rank r. Put B = S^4 x X". The invariant is
Definition 3.2 (p. 11): nu_{X,Q}(v) := [Z(v), sigma_v, f_v] -
[Z(v), sigma_v, c_v] in Omega-tilde^Spin_4(SU(2)).
