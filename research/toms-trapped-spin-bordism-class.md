---
rg: 2
id: toms-trapped-spin-bordism-class
kind: claim
title: Toms's trapped spin-bordism class is a homotopy invariant of unitary sections over S^4 x X and equals the Euler number times the seed class
distinct_from:
  stw59-simple-ah-non-k1-injective: That detects its order-two unitary by the parity of a twisted section count over S^4 x products of CP^r; this is Toms's separate detector, which restricts a unitary section to its block-diagonal locus and takes the spin bordism class of the protected block.
artifacts:
  - research/artifacts/toms-lix-k1-injectivity-import-2026-09-12.md
  - research/artifacts/class-three-spin-bordism-trapping-2026-09-12.md
---

Import from A. S. Toms, arXiv:2609.09535v1 (unrefereed preprint, 8 Sep 2026).

Let X be a closed, simply connected spin manifold of dimension 4r, and
Q -> X a Hermitian bundle of rank r. Put B = S^4 x X, E = C^2 (+) Q and
W = Hom(Q, C^2) ≅ Q* (+) Q*. For a unitary section v transverse to the
block-diagonal subbundle, Z(v) is its block-diagonal locus. It is a spin
four-manifold, and its upper-left block gives f_v: Z(v) -> SU(2). The class

    nu_{X,Q}(v) = [Z(v), f_v]_red  in  Omega-tilde^Spin_4(SU(2)) ≅ Z/2

depends only on the path component of v (Theorem 3.3). Moreover
nu(1_E) = 0 and nu((u o pr_{S^4}) (+) 1_Q) = <c_r(Q)^2, [X]>·eta_Spin
(Proposition 4.2).

The same paper provides the Grassmannian recursion
X_{i+1} = X_i x Gr_2(C^{2d_i+2}), which keeps dim X_i = 4 rank Q_i and
<c_{r_i}(Q_i)^2, [X_i]> = 1 (Lemma 5.1, Proposition 5.2). It also gives the
fullness criterion for simplicity (Lemma 6.3) and finite-stage detection of
null-homotopy in injective limits (Lemma 7.1).
