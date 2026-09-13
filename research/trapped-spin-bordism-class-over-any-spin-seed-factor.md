---
rg: 2
id: trapped-spin-bordism-class-over-any-spin-seed-factor
kind: claim
title: Toms's trapped spin-bordism class works over M x X for any closed spin seed manifold M and multiplies [M, f] by the Euler number
distinct_from:
  toms-trapped-spin-bordism-class: That is Toms's statement for the seed factor S^4 and simply connected base; this replaces S^4 by any closed spin M of any dimension with a fixed spin structure, and takes values in Omega-tilde^Spin_(dim M)(SU(2)).
artifacts:
  - research/artifacts/class-three-spin-bordism-trapping-2026-09-12.md
---

Let M be a closed smooth m-manifold with a fixed spin structure. Let X be a
closed, simply connected spin manifold of dimension 4r and Q -> X a
Hermitian bundle of rank r. Put B = M x X, E = C^2 (+) Q and
A = Gamma(End E). The trapped class of Toms (Definition 3.2 of
arXiv:2609.09535v1), computed with the product spin structure on B, defines
a function

    nu^M_{X,Q}: U(A)/U_0(A) -> Omega-tilde^Spin_m(SU(2)).

It vanishes on 1_E. For every smooth f: M -> SU(2),

    nu^M((f o pr_M) (+) 1_Q) = <c_r(Q)^2, [X]>·[M, f]_red.

Complete argument; not independently reviewed.
