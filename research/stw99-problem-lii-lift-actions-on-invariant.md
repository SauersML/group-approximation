---
rg: 2
id: stw99-problem-lii-lift-actions-on-invariant
kind: claim
title: Actions of amenable groups on the total invariant lift to actions on the algebra (STW Problem LII, after Blackadar)
root: true
artifacts:
  - research/artifacts/stw99-actions-classification-cluster-2026-08-30.md
  - research/artifacts/stw99-lii-equivariant-ehs-obstruction-2026-08-30.md
---

**Problem LII of Schafhauser--Tikuisis--White, arXiv:2506.10902.**
When does an action of a countable discrete amenable `G` on
`K̲T_u(A)` (or `KT_u(A)`) of a unital classifiable `A` lift to an
action on `A`?  Blackadar's original form (order-`n` automorphisms of
scaled ordered `K_0` of AF algebras) is open even for `n = 2`, `A`
simple.

Known: `G` free — yes (CGSTW Thm 9.8 existence for automorphisms);
`G` finite with `A ≅ A ⊗ M_{|G|^∞}` — yes with the Rokhlin property
(Barlak--Szabo + CGSTW Thm 9.14); cyclic groups on UCT Kirchberg
algebras via model building (Katsura); `KT_u`-actions extend to
`K̲T_u`-actions (Nielsen), so the `K̲T_u` form implies the `KT_u`
form.

## Attempts

* The known positive mechanisms are exactly two: bake the symmetry
  into a model and classify (Katsura; Blackadar's CAR symmetry), or
  Rokhlin-average against UHF absorption (Barlak--Szabo).  The
  simple-AF `n = 2` case sits in neither: no `M_{2^∞}`-absorption is
  given, and AF model-building with a prescribed involution on a
  dimension group hits the classical Effros--Handelman--Shen problem
  WITH symmetry — realizing a `Z/2`-dimension-group as the invariant
  of a `Z/2`-AF-system, i.e. an equivariant EHS theorem.  That is a
  purely ordered-`K_0` statement (direct limits of `Z/2`-actions on
  `Z^n` with positivity), recorded as the honest bottleneck.  UPDATE: the
  equivariant-EHS strategy is now REFUTED in general
  (`equivariant-ehs-fails-for-sign-involutions`): sign summands give
  `H^1(Z/2, K_0) ≠ 0`, impossible for limits of permutation stages,
  so lifts of such involutions must be Blackadar-exotic (they preserve
  no finite-dimensional nest); the explicit `(Z^3, θ)` witness is the
  sharp test case for Blackadar's question, and the equivariant-EHS
  route survives only on the `H^1 = 0` locus (where a proof would
  still settle the finite cyclic cases by the same induction).
