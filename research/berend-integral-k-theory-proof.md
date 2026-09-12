---
rg: 2
id: berend-integral-k-theory-proof
kind: route
title: Compute both integral PV sequences and track the torus volume class through all quotient maps
target: berend-integral-k-theory-and-invisible-class
requires:
  - berend-torus-actions-give-strongly-qd-polycyclic-groups
  - berend-proper-quotients-have-decomposition-rank-at-most-two
artifacts:
  - research/artifacts/berend-k-theory-quotient-obstruction-2026-09-05.md
---

For `D=C(T^3)` the action of a lattice automorphism on `K_*(D)` is
its integral exterior action. The chosen cubic gives
`det(1-alpha)=-1` and `det(1-Lambda^2 alpha)=1`, so the degree-one and
degree-two terms of `1-alpha_*` are integral isomorphisms. The first
Pimsner--Voiculescu sequence gives `K_1(B)=Z omega_B + Z[u_alpha]`,
where `B=D ⋊_alpha Z`. The second generator acts by
`diag(epsilon,1)` on these exact generators.

The first sequence also gives `K_0(B)=Z[1] + Z eta`. To remove a
potential extension shear, evaluate at the fixed torus point zero to
obtain `r:B -> C(T)` and choose `r_*(eta)=0`. Naturality of the PV
boundary then forces `beta_*(eta)=epsilon eta`. Thus the action on
`K_0(B)` is `diag(1,epsilon)`. The second PV sequence yields the asserted
K-groups, and injects `Z/(1-epsilon)Z omega_B` into `K_1(A)`, proving
the exact order of `nu`.

Every proper quotient factors through a finite-orbit restriction, which
kills the image of `K_1(D)` because `K_1(C(F))=0`. The ideal assertion
then follows from the extension six-term exact sequence. For the product
assertion, choose a fixed matrix representative `v` of the top class.
Each finite evaluation of `v` has a selfadjoint logarithm of norm at
most `pi`; their uniformly bounded product gives a single
norm-continuous nullhomotopy in the product algebra. The artifact gives
the complete proof and sign audit.
