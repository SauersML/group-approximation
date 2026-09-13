---
rg: 2
id: hyperlinear-implies-sofic-via-frame-extraction
kind: route
title: Extract a frame for G * Z; its phases can only separate an abelian normal subgroup, and G * Z has none
target: hyperlinear-implies-sofic
requires:
  - hyperlinear-groups-admit-masa-normalizing-microstates
  - block-monomial-hs-models-sofic-mod-amenable-soft-kernel
  - diagonal-normalizer-rigidity
  - hyperlinear-groups-closed-under-free-products
artifacts:
  - research/artifacts/ex-q34-frame-extraction-2026-09-12.md
---

Let `H` be hyperlinear and `H != 1`.  Put `Γ = H * Z`.

1. `Γ` is hyperlinear (`hyperlinear-groups-closed-under-free-products`).
2. By `hyperlinear-groups-admit-masa-normalizing-microstates`, `Γ` has regular
   HS microstates with `def_D -> 0` for a full masa.  `diagonal-normalizer-rigidity`
   clause 1 moves them to monomial unitaries at cost `3 sqrt(def_D)`, which keeps
   them regular.  So `Γ` has an injective regular homomorphism into the
   monomial ultraproduct `prod_omega U(1) wr S_n`.
3. By `block-monomial-hs-models-sofic-mod-amenable-soft-kernel` with `k = 1`,
   the soft kernel `A` is an abelian normal subgroup of `Γ` and `Γ/A` is
   sofic.
4. `Γ` has no nontrivial abelian normal subgroup (artifact Lemma 4a, from the
   classical commuting-elements theorem and malnormality of factors in free
   products).  So `A = 1`, `Γ` is sofic, and so is its subgroup `H`.

This is an equivalence, not a new hypothesis: conversely, sofic
approximations are permutation matrices, which normalize the diagonal masa.
The route's content is what it removes.  The `U(1)`-phases of a monomial
model, their cocycle identities and every trace cancellation they produce are
irrelevant to Q3.4.  The first premise is the single remaining obstruction:
an approximately invariant frame.
