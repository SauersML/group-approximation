---
rg: 2
id: pointwise-hs-stability-from-no-hyperlinear-quotient
kind: claim
title: The missing HS slot of the mixed-approximation stability trio
distinct_from:
  leavitt-steinberg-hs-stable: That is the open branch selection for one explicit group; this is the unconditional general implication whose hypothesis that branch supplies.
  invariant-size-collapse: That is an exact algebraic collapse under a monotone invariant size; this is a stability statement about almost-representations in the normalized-HS metric.
  steinberg-hyperfinite-hs-stable: That is the proved hyperfinite restriction for one group; this is the general pattern in the full metric, with a hypothesis nobody has verified for any infinite group.
artifacts:
  - GroupApproximation/Stability/MixedApproximation.lean
  - GroupApproximation/Sofic/HyperlinearUltraproduct.lean
---

If every hyperlinear quotient of `G` is trivial, then `G` is pointwise
normalized-HS stable: every sequence of maps `phi_n:G -> U(d_n)` whose
multiplicative defects vanish pointwise in `‖.‖_(2,d_n)` converges pointwise
to `1`, and the trivial representations witness stability.

The point of stating it is architectural.
`GroupApproximation/Stability/MixedApproximation.lean` already formalizes the
same implication twice, in the other two metrics, by one three-line pattern:

- `HasNoNontrivialMixedQuotient.isPointwisePStable` (`:300`), via
  `hammingAlmostRepresentation_trivial`;
- `HasNoNontrivialMixedQuotient.isPointwiseOperatorNormStable` (`:380`), via
  `opAlmostRepresentation_trivial` and
  `normMatrixCoronaUnitary_isOperatorMF`.

Both proofs read the almost-representation in the ultraproduct or corona,
observe that **the target itself belongs to the approximation class**, and
conclude that the induced homomorphism is trivial.  The file's class is
`IsMixedApproximable G := IsSofic G ∨ IsOperatorMF G` (`:38`); hyperlinearity
is absent from it, and there is no `HSAlmostRepresentation`, no
`IsPointwiseHSStable`, and no lemma asserting that the unitary group of a
tracial matrix ultraproduct is hyperlinear.  That last lemma -- the analogue
of `normMatrixCoronaUnitary_isOperatorMF` -- is the only missing ingredient;
`GroupApproximation/Sofic/HyperlinearUltraproduct.lean` already carries
`HyperlinearApproximation` (`:227`) and the bridge
`isHyperlinear_of_hyperlinearUltraproductEmbedding`.

Two consequences worth having explicit.

**The HS slot is the hardest of the three by construction.**  Soficity
implies hyperlinearity, so "no nontrivial hyperlinear quotient" is strictly
stronger than "no nontrivial sofic quotient".  The trio is not three
comparable problems; the metric in which the hypothesis is hardest to
satisfy is exactly the one left open.

**For `U=St_5(L_(F_2)(1,2))` the hypothesis is the fork.**  `U` is
quasisimple, so a nontrivial hyperlinear quotient is a central quotient, and
`leavitt-steinberg-hs-stability-fork` makes the existence of one equivalent
to hyperlinearity of `Q=EL_4(L_(F_2)(1,2))`.  So `leavitt-steinberg-hs-stable`
is precisely the missing hypothesis of a third instance of an
already-formalized pattern, and its formalization would be a copy of the two
existing proofs -- which is a real statement about where the difficulty is
not.
