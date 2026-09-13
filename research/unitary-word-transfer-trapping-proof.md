---
rg: 2
id: unitary-word-transfer-trapping-proof
kind: route
title: Run the trapping tower with protected block C^p, base point, and quaternionic Grassmannian steps Gr_m(H^{m+pd})
target: unitary-word-transfer-to-simple-ah-via-trapping
requires:
  - trapped-lambda-mod-eight-class-over-seed-factor
  - quaternionic-grassmannian-trapping-defect-is-rank
  - toms-trapped-spin-bordism-class
artifacts:
  - research/artifacts/class-four-lambda-mod-eight-trapping-part3-2026-09-13.md
  - research/artifacts/class-four-lambda-mod-eight-trapping-part2-2026-09-13.md
---

Part 3, Section 7.

Detector (Proposition 7.1). Take E = C^p (+) Q over M x X with dim X = 2p·rank Q,
and suppose TX − Hom(Q, C^p)_R carries a Spin_m-structure. The rank-two
argument works verbatim with C^p. The normal bundle of the block-diagonal
locus is canonically Hom(Q, C^p)_R. The structure restricts from
TB − W_R. On M x {zero}, the structure over a point is an orientation. It
gives nu((f o pr) (+) 1_Q) = ±<c_r(Q)^p, [X]>·[M, f]_red and nu(1) = 0.

Steps (Lemma 7.2). Here G = Gr_k(H^{k+pd}) and Q_G = d·zeta. The Pieri count
is sigma_{1^k}^{pd} = [pt]. The defect is
lambda(TG) − lambda(W_R) = −(pd − k)·q_1 + pd·q_1 = k·q_1, so k = m works.

Tower. Start with X_1 = point and A_1 = C(M, M_p). Step by
X_{i+1} = X_i x Gr_m(H^{m + p d_i}), with Toms's evaluation connecting maps.
The count ±1 and the Spin_m-structure persist. The word is computed
pointwise, so its image at stage i is homotopic to (f o pr) (+) 1_{Q_i},
whose trapped class is ±[M, f]_red != 0. Toms Lemmas 6.3 and 7.1 give
simplicity and keep the word outside U_0(A).
