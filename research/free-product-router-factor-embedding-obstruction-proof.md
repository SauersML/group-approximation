---
rg: 2
id: free-product-router-factor-embedding-obstruction-proof
kind: route
title: Injective plus surjective factor maps collapse the defect
target: free-product-router-factor-embedding-obstruction
requires: []
artifacts:
  - GroupApproximation/Sofic/SmallCancellationRouter.lean
---

## Complete argument

Let `q : E ∗ B → Q` be a quotient in a regime with factor embedding, and
suppose the `RoutingLemmaData` fields hold for `q`.

1. `partner_surjective` says `q|_B : B → Q` is onto; factor embedding
   says it is injective; so `q|_B` is an isomorphism.
2. `route_surjective` and factor embedding on `E` give `q|_E : E ≅ Q`
   the same way.
3. `defect_top` says `Subgroup.map (q|_E) N = ⊤`.  Take any `e ∈ E`.
   Then `q e ∈ ⊤ = (q|_E)(N)`, so `q e = q n` for some `n ∈ N`, and
   injectivity of `q|_E` gives `e = n`.  Hence `N = ⊤`.
4. The routing lemma's source is required to have a nontrivial PROPER
   defect (the bare HNN skeleton of [[concrete-compression-source]] has
   `N ≠ ⊤`: the quotient of the skeleton by `N` is the group in which
   the transported mark commutes with the base, which is visibly
   nontrivial — it retains the base and stable letter).  Contradiction.

The order-preserving variant: if `orderOf (q x) = orderOf x` for every
`x`, then `x ∈ ker q` gives `orderOf x = orderOf (q x) = orderOf 1 = 1`,
so `x = 1`; the derived surjectivity of the routing map plus step 3
again force `N = ⊤`.  This half is being machine-checked as the
degeneracy lemma of the W0 interface wave; the artifact records the
interfaces it constrains.
