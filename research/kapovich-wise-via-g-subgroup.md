---
rg: 2
id: kapovich-wise-via-g-subgroup
kind: route
title: Derive the finite-quotient equivalence using a free residual subgroup and Olshanskii's theorem
target: kapovich-wise-rf-iff-finite-quotients
requires:
  - olshanskii-g-subgroup-quotient-theorem
artifacts:
  - research/artifacts/hyperbolic-quotientless-kazhdan-proof-2026-09-11.md
---

The artifact, Sections 1--3, proves this implication completely from the
stated small-cancellation input. Given a hyperbolic group `A` and a
nonidentity element killed by every finite homomorphism, form the free
product `C` of six copies. If `a_i` are its six copies, then
`L = <a_1 a_2 a_3, a_4 a_5 a_6>` is a free rank-two subgroup contained in
the finite residual of `C`.

The Bass--Serre tree for the splitting into the two triple products has
trivial edge stabilizers. A nontrivial finite subgroup has one fixed vertex;
its normalizer preserves that vertex. Since `L` contains a tree translation,
it normalizes no such finite subgroup. Hence `E_C(L) = E(C) = 1`, so `L` is
a `C`-subgroup. Olshanskii gives a non-elementary word-hyperbolic quotient
onto which `L` surjects. Every finite homomorphism of this quotient vanishes
because its pullback kills `L`.

Thus failure of universal residual finiteness implies failure of universal
existence of nontrivial finite quotients. The converse is immediate from the
definition of residual finiteness. This is a proof of the known
Kapovich--Wise equivalence, with Olshanskii's theorem as an explicit
prerequisite.
