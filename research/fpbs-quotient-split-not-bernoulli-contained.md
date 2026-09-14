---
rg: 2
id: fpbs-quotient-split-not-bernoulli-contained
kind: claim
title: An action with a nontrivial factor fixed by a nonamenable normal subgroup is not weakly contained in the Bernoulli shift
invalidates:
  - fpbs-dead-split-cost-one-weak-containment-transfer
distinct_from:
  fpbs-source-statistics-not-reproducible-in-bernoulli: that rules out reproducing an invariant two-point label inside a strongly ergodic Bernoulli action; this rules out every action with a nontrivial factor on which a nonamenable normal subgroup acts trivially, through the restriction of the Koopman representation to that subgroup.
artifacts:
  - research/artifacts/fpbs/docs/normal-subgroup-fixed-price.md
---

**Proposition B of the linked note.** Let `N` be a nonamenable normal subgroup
of a countable group `Gamma`, and let `alpha` be a p.m.p. action of `Gamma`
with a nontrivial factor on which `N` acts trivially. Then `alpha` is not
weakly contained in the Bernoulli shift `b_Gamma` on `[0,1]^Gamma`.

**Proof outline.**
* Pulling back a mean-zero function from the factor gives an `N`-invariant
  unit vector in `L^2_0` of `alpha`.
* Weak containment of actions implies Zimmer weak containment of the Koopman
  representations on `L^2_0`, because coefficients of simple functions only
  involve finitely many intersection measures.
* The Koopman representation of `b_Gamma` on `L^2_0` is a direct sum of
  quasi-regular representations `l^2(Gamma/K)` with `K` finite: finite tensor
  products of basis functions are permuted with finite stabilizers. It is
  therefore contained in a multiple of `lambda_Gamma`, whose restriction to
  `N` is a multiple of `lambda_N`.
* So the trivial representation of `N` would be weakly contained in
  `lambda_N`, and `N` would be amenable.

**Consequence.** Every quotient-split action of
`fpbs-quotient-split-actions-have-cost-one` with nontrivial quotient factor
fails to be weakly contained in `b_Gamma` when `N` is nonamenable. So the cost
one of those actions cannot be passed to the maximal-cost Bernoulli action
through monotonicity of cost under weak containment. For infinite amenable
`N` the group already has fixed price one by Gaboriau's weakly normal
criterion.
