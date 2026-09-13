---
rg: 2
id: penrose-derived-full-group-homology-is-finitely-generated
kind: claim
title: The Penrose derived full group has H_2 = Z plus a finite 2-group and finitely generated homology in every degree, so homology and additive relation invariants cannot refute its finite presentation
invalidates:
  - penrose-not-fp-via-infinitely-generated-homology
  - penrose-not-fp-via-mean-area-relation-invariant
distinct_from:
  penrose-derived-full-group-is-finitely-presented: That is the open finite presentation question; this proves that the homological and additive-invariant obstructions to it vanish, which neither establishes nor refutes it.
  z2-derived-full-group-h2-fg-iff-mod-two-cohomology-finite: That is the criterion for free minimal Z^2-actions; this is the computation for the Penrose tiling groupoid, which acts through Z^2 ⊕ Z/5 and is handled through Li's groupoid homology of the Penrose tiling.
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `𝒫` be the Chornyi–Juschenko–Nekrashevych Penrose tiling group
(`penrose-tiling-group-is-an-amenable-orbit-full-group`) and `D(𝒫)` its derived subgroup.

1. `H_2(D(𝒫); Z) ≅ Z ⊕ T`, where `T` is an abelian 2-group of exponent at most 4 and order `2^12`
   or `2^13`.
2. `H_j(D(𝒫); Z)` is finitely generated for every `j`.
3. **Additive relation invariants.** Let `F` be free on a finite generating set of `D(𝒫)` and `N`
   the relation subgroup. Every homomorphism `alpha : N -> A` that is invariant under conjugation
   by `F` has finitely generated image.
   - An example is the mean signed area `alpha(w) = ∫ A(w, x) dμ(x)` of the marked-vertex loop of
     a relator `w`, against the invariant measure `μ`.

**Consequence.** No argument of the form "`H_j(D(𝒫))` is infinitely generated" can prove that
`D(𝒫)` is not finitely presented, or not of type `F_∞`.
- **Additive invariants.** Nor can "some conjugation-invariant additive invariant of relations
  takes infinitely generated values", which includes the invariant-measure obstructions to
  relation compression.
- **What remains.** A proof of non-finite presentation must be nonabelian: LEF, rigidity on defect
  models, or non-spatial marked approximants.

Proof: `penrose-derived-full-group-homology-proof`.
