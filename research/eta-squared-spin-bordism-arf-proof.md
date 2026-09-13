---
rg: 2
id: eta-squared-spin-bordism-arf-proof
kind: route
title: The commutator is 1 on the fat wedge, so a regular preimage is a framed torus representing eta squared, with Arf invariant one
target: eta-squared-commutator-has-nonzero-spin-bordism-class
requires:
  - u2-triple-samelson-class-three-stage
artifacts:
  - research/artifacts/class-three-spin-bordism-trapping-2026-09-12.md
---

Commutators with 1 vanish. So c ≡ 1 on the fat wedge
F = {s_1 = 1} ∪ {s_2 = 1} ∪ {z = 1}, and c descends to
cbar: S^5 = (T^2 x S^3)/F -> SU(2). The prerequisite gives
[cbar] = omega o eta_3 o eta_4, the generator of pi_5(S^3) = Z/2.

Take a regular value y != 1. The preimage L = c^{-1}(y) lies in the open cell
T^2 x S^3 \ F ≅ R^5, where the ambient spin structure is unique. So the spin
structure on L comes from the normal framing alone, whatever structure was
chosen on T^2. By Pontryagin--Thom, (L, framing) represents the
stabilization of [cbar]. Freudenthal makes pi_5(S^3) -> pi_2^s onto, and both
groups are Z/2, so that stabilization is eta^2 != 0.

The ring isomorphism of Pontryagin--Thom represents eta^2 by the product of
two Lie-framed circles. Each carries the nonbounding spin structure (Toms
arXiv:2609.09535v1, Lemma 2.6 and its proof). Their product is the spin
torus whose quadratic form is 1 on all three nonzero classes. Its Arf
invariant is 1, so the class is nonzero in Omega^Spin_2 ≅ Z/2. The suspension
isomorphism Omega-tilde^Spin_5(S^3) ≅ Omega^Spin_2 is given by regular
preimages, as in Toms (6) and (8). So [T^2 x S^3, c]_red != 0.
