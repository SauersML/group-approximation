---
rg: 2
id: self-square-embedding-gives-a-kazhdan-clifford-base-proof
kind: route
title: Split the injection into its two factors, then feed it to the construction
target: self-square-embedding-gives-a-kazhdan-clifford-base
requires: []
artifacts:
  - GroupApproximation/Monsters/FournierFacioRealization.lean
  - GroupApproximation/Monsters/RealizationEmbedding.lean
---

## Why sufficient

Machine-checked, no `sorry`, no axiom, no literature premise in the chain that
this route commits to.

**The algebra.**  `selfEmbeddingEndomorphism f = f o inl` and
`secondFactorEmbedding f = f o inr`; `secondFactorElement f b = f (1, b)`.  Then
`rem_ff_realization_alpha_injective` and `rem_ff_realization_beta_injective`
(injectivity of both factors, from injectivity of `f` and of the coproduct
inclusions), `rem_ff_realization_a_notMem_range` (if `f (1, b) = f (p, 1)` then
`(1, b) = (p, 1)`, so `b = 1`), `rem_ff_realization_factors_commute` (the two
factors commute because `inl p` and `inr q` do), and
`rem_ff_realization_factors_disjoint` (the ranges intersect trivially, same
argument as the non-membership).  The two range subgroups are the remark's
`P_1`, `P_2`, and `rem_ff_realization_firstFactorEquiv` /
`rem_ff_realization_secondFactorEquiv` identify each with `P`.

**The construction consumes it.**  `rem_ff_realization_not_isCDEOperatorMF`,
`rem_ff_realization_base_injective` and `rem_ff_realization_finitelyPresented`
are the corresponding projections of `kazhdanCliffordConstruction` applied to
`(alpha, a)`, quantified over every finitely presented property-(T) base
carrying such an `f`.

**The involution.**  `rem_ff_realization_contains_involution` returns the
distinguished `mark`, with `mark != 1` and `mark^2 = 1` from the construction's
own output — no hypothesis on the base beyond what the construction already
needs.

**Non-vacuity.**  `exists_properSelfEmbedding`: for any nontrivial group `A`,
the group `Pi_N A` embeds its own direct square by interleaving
(`interleave`, `piSelfSquareEmbedding`, `piSelfSquareEmbedding_injective`), and
the embedding is proper.  So the algebraic hypothesis consumed above is
inhabited, unconditionally, and the pair `(alpha, a)` genuinely exists.

**The universality step, with its hypothesis showing.**
`rem_ff_realization_selfSquareEmbedding_of_universal` takes `huniv` — "every
finitely presented torsion-free group embeds in `P`" — as an explicit
hypothesis and concludes `P x P` embeds in `P`, using
`ProductFinitePresentation.instProd` and `IsPowerTorsionFree.prod`.  That
hypothesis is the literature input, and it is the only place it appears; it does
not leak into any other declaration in this route.

## Why the target is `requires: []` despite that hypothesis

The claim asserts the implication *from* a self-square embedding, plus the
unconditional existence of groups admitting one.  Both are closed theorems.  The
universality statement is not part of the claim — it is the route by which one
*particular* group would be shown to satisfy the hypothesis, and the claim is
deliberately stated so that no such group is needed.
