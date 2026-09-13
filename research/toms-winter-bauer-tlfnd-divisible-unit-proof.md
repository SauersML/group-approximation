---
rg: 2
id: toms-winter-bauer-tlfnd-divisible-unit-proof
kind: route
title: Divided unit gives rank density on Bauer simplices, and the established comparison chain turns it into Gamma and Z-stability
target: toms-winter-bauer-tlfnd-iff-tracially-divisible-unit
requires:
  - bauer-tracially-divisible-unit-gives-bounded-rank-density
  - strict-comparison-compares-ultrapower-projections
  - ultrapower-comparison-with-rank-density-divides-projections
  - strict-comparison-with-rank-density-gives-support-projections
  - uniform-gamma-iff-tracial-support-projections-and-division
  - uniform-gamma-algebras-satisfy-toms-winter
  - strict-comparison-unit-divisibility-equivalences
artifacts:
  - research/artifacts/ex-toms-winter-bauer-divisible-unit-2026-09-12.md
  - research/artifacts/ex-toms-winter-bauer-divisible-unit-part2-2026-09-12.md
  - research/artifacts/ex-toms-winter-unit-divisibility-equivalences-2026-09-12.md
---

Let `A` be unital, simple, separable, nuclear and non-elementary, with Bauer
`T(A)`, tlfnd and strict comparison.

1. **(e) ⟹ (c).** `bauer-tracially-divisible-unit-gives-bounded-rank-density`.
2. **(c) ⟹ (b).**
   - `strict-comparison-compares-ultrapower-projections` (nuclear implies exact)
     gives PC in every `M_k(A^U)`.
   - `ultrapower-comparison-with-rank-density-divides-projections` turns PC and RD_b
     into PD.
   - `strict-comparison-with-rank-density-gives-support-projections` gives TSP.
   - Part (b) of `uniform-gamma-iff-tracial-support-projections-and-division`
     gives uniform Gamma from TSP, PD and tlfnd.
3. **(b) ⟹ (a).** `uniform-gamma-algebras-satisfy-toms-winter` (CETW Theorem A).
4. **(a) ⟹ (d).**
   - `Z` has a unique trace with `π_{τ_Z}(Z)'' ≅ R`. Kaplansky density and order
     zero lifting give order zero `φ_m: M_N → Z` with `τ_Z(1 − φ_m(1)) → 0`.
   - Every trace of `A ⊗ Z` restricts to `τ_Z` on `1 ⊗ Z`, so `1 ⊗ φ_m` is
     tracially large. Transport it through `A ⊗ Z ≅ A`.
   - Lift and push forward through `ℓ^∞(A) → A^U` (Definition 1.1 of the artifact).
5. **(d) ⟹ (e).** Trivial.
6. **(e) ⟺ (f) ⟺ (g).** `strict-comparison-unit-divisibility-equivalences`
   (nuclear implies exact).
7. **Counterexample clauses.**
   - Negating (d), (e) and (f) gives the indivisible unit.
   - The projection clause uses the PC-only Steps 3–6 of Theorem 2 in
     `research/artifacts/tw-invisible-gamma-support-gap-2026-09-12.md`.
   - Lemma 3.1 of part 2: a unital simple infinite-dimensional unique-trace
     subalgebra gives (e).
   - Lemma 3.2 of part 2: an explicit order zero `M_N → Z_{n,n+1}` of fibrewise
     trace at least `1 − N/n` gives (e) from unital `Z_{n,n+1}` for large `n`.

**Corroborating chain for step 2.** RD_b gives rank density. Strict comparison
then gives purity (`rank-density-and-strict-comparison-give-purity`). Lin's pure
dichotomy gives stable rank one, and Vaccaro's Theorem B (arXiv:2604.24682v2,
lines 89–91, read on MSI) gives uniform Gamma under tlfnd.
