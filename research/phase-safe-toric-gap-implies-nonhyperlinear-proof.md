---
rg: 2
id: phase-safe-toric-gap-implies-nonhyperlinear-proof
kind: route
title: Central phase projection turns a hyperlinear embedding into a perfect finite-dimensional strategy
target: phase-safe-toric-gap-implies-nonhyperlinear
requires: []
artifacts:
  - docs/TRUE_NORMAL_TORIC_GAP_IMPLIES_NONHYPERLINEAR.md
---

Direct proof, written out in `docs/TRUE_NORMAL_TORIC_GAP_IMPLIES_NONHYPERLINEAR.md`
§2 and summarized in the claim.  Steps: `N ∩ B = {1}` embeds `B` centrally in
`Q = Gtilde/N`; form `p_chi = |B|^{-1} sum_b conj(chi(b)) lambda_Q(b)`, a
central projection of trace `1/|B|`; a hypothetical hyperlinear model of `Q`
makes the corner `p_chi L(Q)` Connes embeddable; on that corner the clauses
hold exactly, so the corner trace is a perfect commuting strategy; embedding
into a matrix ultraproduct and realizing the commuting pair as left and right
multiplication on Hilbert--Schmidt space converts it to a finite-dimensional
tensor strategy with value tending to `1`, contradicting `omega_qa < 1`.

Only Watts--Helton--Klep's *definition* of torically determined is imported;
their Theorem 5.12 is used for orientation and is not a premise of the
implication.  No stability input, no approximate-representation decoder.
