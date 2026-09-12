---
rg: 2
id: kazhdan-jones-uniform-carrier-containment-proof
kind: route
title: Apply the Kazhdan projection estimate to the Jones projection of the target subalgebra
target: kazhdan-generator-containment-is-uniform-on-the-group
requires: []
artifacts:
  - research/artifacts/kazhdan-jones-uniform-carrier-containment-2026-09-08.md
---

In the basic construction N=<M,e_B>, use the canonical semifinite
trace Tr(x e_B y)=tau(xy). Thus Tr(e_B)=1 even when Tr(1) is infinite.
Conjugation by rho(C) is a genuine unitary representation alpha on
L^2(N,Tr), and direct use of e_B x e_B=E_B(x)e_B gives

    ||alpha(c)e_B-e_B||_(2,Tr)^2
      =2(1-||E_B(rho(c))||_2^2)
      =2 dist_2(rho(c),B)^2.

If P is the invariant-vector projection, then for every c in C,

    ||alpha(c)e_B-e_B|| <= 2||e_B-Pe_B||
      <= (2/kappa)max_(s in S)||alpha(s)e_B-e_B||.

Cancel sqrt(2) to obtain (KJC1). Triangle inequality proves (KJC2),
and orthogonality of conditional expectation gives
||E_B(V)||_2^2=1-dist_2(V,B)^2 for every unitary V. The proof and the
source identities are expanded in the artifact.
