---
rg: 2
id: sl3z-maps-to-cocompact-lattices-have-finite-image
kind: claim
title: Every homomorphism from a finite-index subgroup of SL3(Z) into a cocompact lattice of SL3(R) has finite image
distinct_from:
  bms-sln-z-representations-agree-with-algebraic-ones: that is rational rigidity, which forces finite image only for lattices with a unipotent-free rational representation (hypothesis (R)); this uses real superrigidity and needs only cocompactness of the target
---

**ESTABLISHED (unreviewed).** Let `Γ'` be a finite-index subgroup of `SL_3(Z)` and `Λ <= SL_3(R)` a cocompact
lattice. Then every homomorphism `ρ : Γ' → Λ` has finite image.

**Consequence.** Every place where hypothesis (R) of `sl3z-cocompact-quotient-uniformly-far-from-finite-actions`
was used only to make holonomy homomorphisms `Γ_v → Λ` finite now works for every cocompact lattice. This
covers:
* Theorem E itself, recorded as `sl3z-every-cocompact-quotient-far-from-finite-actions`;
* step 5 of `sl3z-cocompact-not-factor-of-bernoulli-times-profinite-proof`;
* step 3 of `sl3z-cocompact-exclusion-from-almost-cocycle-rounding`.

So the division-algebra hypothesis can be dropped throughout.

**Remark (not used).** The same argument shows finite image into any lattice not commensurable with a
conjugate of `SL_3(Z)`. It needs the classification of continuous automorphisms of `SL_3(R)` (inner ones,
and inverse transpose; recalled) in place of the compactness argument of step 3.

Proof in `sl3z-maps-to-cocompact-lattices-have-finite-image-proof`.
