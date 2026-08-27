---
rg: 2
id: free-product-router-factor-embedding-obstruction
kind: claim
title: Factor embedding makes classical free-product small cancellation unusable for the router
distinct_from:
  bespoke-routing-lemma: that claim asserts a routing lemma EXISTS in some elementary regime; this one delimits the regime — the classical syllable-metric free-product C'(1/6) theory, whose Greendlinger conclusion the repository itself uses to prove factor embedding, can never produce the router's surjectivity fields.
artifacts:
  - GroupApproximation/Sofic/SmallCancellationRouter.lean
  - GroupApproximation/Sofic/OsinRelativeSmallCancellation.lean
---

Any small-cancellation regime over the free product `E ∗ B` strong
enough to yield the classical factor-embedding property cannot
instantiate `RoutingLemmaData`.  Factor embedding — the natural maps of
the factors into the quotient are injective, which the repository's own
consequence layer derives from `GreendlingerLengthBound` in
`OsinRelativeSmallCancellation.lean` — combines with the router's field
`partner_surjective` to force `q|_B` to be an isomorphism `B ≅ Q`; with
`route_surjective` and factor embedding on the `E` side it likewise
forces `E ≅ Q`.  Then `defect_top` (`Subgroup.map q N = ⊤` with `q|_E`
injective) forces `N = ⊤` already in `E`: for `e ∈ E` pick `n ∈ N` with
`q e = q n`, so `e = n`.  A compression source with proper nontrivial
defect therefore admits NO routing datum in any factor-embedding
regime.  The same argument shape kills the order-preserving interface:
a routing map preserving every element order has trivial kernel, and
surjectivity plus `defect_top` again force `N = ⊤` — so
`OrderPreservingRoutingData` (the manuscript's "preserves element
orders" phrase) is degenerate, and the honest discharge target is the
injectivity-based `DefectRoutingData` chain.

Consequence, positive direction: a proof of
[[bespoke-routing-lemma]] must use relator families that BREAK factor
embedding by design.  The relative CoprodI machinery is thereby off the
critical path for the router; the working architecture is the free-group
avatar presentation of [[free-group-avatar-router]], where the quotient
is presented over a rank-two free group and the factor maps are defined
by long target words rather than induced by inclusions — injectivity of
the factor maps is never true and never needed.
