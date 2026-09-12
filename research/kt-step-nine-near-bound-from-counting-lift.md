---
rg: 2
id: kt-step-nine-near-bound-from-counting-lift
kind: claim
title: Near bound of the Kun--Thom step 9 re-separation from the counting lift and estimate (7)
distinct_from:
  kt-step-nine-hamming-estimate-from-actual-defects: that node is the Hamming estimate, which takes the near bound as a hypothesis; this one produces the near bound at a retained object.
  kt-relative-functor-raw-map-defect-estimate: that node bounds defects of the raw map and transports estimate (7) back to the reference arrow; this one combines estimate (7) with the counting lift and the same-cluster gap on the chosen representatives of two bisections.
  kt-matched-bridge-defects-sum-to-one-hamming-count: that node sums bridge equivariance defects over matched blocks; this one is a one-sided disagreement bound between two arrows at one object.
artifacts:
  - GroupApproximation/KunThom/StepNineNear.lean
---

**ESTABLISHED, proved here.** Module `KunThom/StepNineNear`, namespace
`GroupApproximation.BlockPatching`.

**Setting.** This is Kun--Thom, arXiv:2608.06222v3, proof of Theorem 4.1, step 9.
- `D` is scaled cluster data placed disjointly by `ι`, and `q` represents a
  compressor.
- `F` is a functor between the cluster groupoid restricted to the retained objects
  `R` and to their images `D'`.
- Estimate (7) holds along `F` with bound `ε`, for the bridges realized by `q⁻¹`.
- `â` is the bisection representing the almost centralizer, and `b` is its lift.

**Proved.** `card_disagreement_sandwich_lt_of_lift` takes the lift output of
`CountingEndgame.exists_bisection_lift_restrict` at a retained object `x`:
- `F` sends an arrow `g` out of `x` to the arrow of `â` at the image `i` of `x`;
- `b` carries `g` at `x`.

Then for every `π` with `π i = x`, the chosen arrow of `â` at `i` disagrees with
the raw map `sandwich (bridge q⁻¹ (π i) i) (bridge q⁻¹ (b(π i)) (â i)) (b_{π i})`
on fewer than `2 * sc` points, whenever `radius i j + ε x Z ≤ 2 * sc`. This is
the hypothesis `hnear` of
`BlockPatching.BlockArrows.card_hammingDisagreement_patch_conj_le_stepNine`.

For the relative functor of `RelativeFunctorAssembly`:
- `h7` is `GroupoidPresentation.ClusterMetric.twoSidedDisagreement_sandwich_lt_of_ofRep_eq`;
- `ε X Z` is `radius (obj X) (obj Z) + ρ X Z`.

Supporting lemmas:
- `GroupoidPresentation.ClusterMetric.twoSidedDisagreement_lt_of_heq_ofRep`:
  if the classes of two representatives agree after an equality of target
  objects, nearness transfers from one to the other at the cost of one radius;
- `FinitePartialBijection.card_disagreement_le_twoSidedDisagreement`.

## Findings

1. **No expansion enters.** The near bound uses only the distance gap of the
   cluster groupoid and estimate (7). The re-separation that needs expansion stays
   inside step 9, so neither the vanishing threshold nor a fixed expansion
   constant is involved here.
2. **The lift output is only propositionally aligned with the patched arrows.** It
   is stated with `eqToHom` along object equalities. The patched arrows are
   `Quotient.out` representatives indexed by the bisections' object maps. The proof:
   - generalizes the target object of the lift and substitutes the equation `b x = y`;
   - moves both classes across `eqToHom` with `CategoryTheory.comp_eqToHom_heq`;
   - transports nearness across the remaining object equality by `subst` in a
     lemma whose indices are free variables.
3. **The functor is abstract.** The hypothesis `h7` is estimate (7) along any functor
   between restricted presentations. That keeps the long numerical hypotheses of the
   relative functor out of the statement.

Derivation: `kt-step-nine-near-bound-from-counting-lift-proof`.
