---
rg: 2
id: bauer-c-space-strict-comparison-pure-and-z-stable
kind: claim
title: Strict comparison gives purity over Bauer simplices with C-space boundary, and Z-stability there under tracially locally finite nuclear dimension
distinct_from:
  toms-winter-holds-on-bauer-tlfnd-locus: that is the open Toms–Winter statement on every compact Bauer boundary; this proves its case where the boundary has property C.
  stw18-finite-trace-boundary-toms-winter: that proves Z-stability for nuclear algebras with compact finite-dimensional boundary without tlfnd; this needs tlfnd for Z-stability but reaches every C-space boundary, and gives purity for exact algebras.
  bauer-strict-comparison-pure-iff-divisible-unit: that is the equivalence between purity and a divisible unit on every Bauer simplex; this applies it where the unit is proved to divide.
artifacts:
  - research/artifacts/ex-tw-c-space-unit-division-part2-2026-09-13.md
---

**Theorem.** Let `A` be a unital, simple, separable, exact, non-elementary
C*-algebra with strict comparison of positive elements. Suppose `T(A)` is a nonempty
Bauer simplex whose extreme boundary has Haver's property C.
- (a) `A` is pure: its Cuntz semigroup is almost unperforated and almost divisible.
- (b) If `A` is nuclear with tracially locally finite nuclear dimension (Vaccaro,
  arXiv:2604.24682, Definition 1.5), then `A ≅ A ⊗ Z`.

So part (1) of STW XXVII holds on this locus. Toms–Winter holds there among algebras
with tlfnd, which includes every algebra with locally finite nuclear dimension.

**Scope** (Section 4 of the part 2 artifact).
- **Finite-dimensional boundary, nuclear `A`.** Already known
  (`stw18-finite-trace-boundary-toms-winter`).
- **Countable union of closed finite-dimensional compacta, nuclear `A`.** Already given
  by bundle triviality, uniform Gamma and CETW
  (`r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial`).
- **Added: exact non-nuclear algebras.** Purity for them, on every C-space boundary.
- **Added: nuclear algebras with tlfnd.** `Z`-stability on C-space boundaries that are
  not countable unions of closed finite-dimensional compacta.
  - Such compacta are recalled from dimension theory (R. Pol's weakly
    infinite-dimensional compactum, reported to have property C). This was not re-read.

**Model test.**
- Villadsen's type I algebras fail strict comparison, so they fail the hypothesis;
  they are not pure.
- Every `Z`-stable algebra with a finite-dimensional Bauer boundary satisfies (a) and (b).

Not reviewed.
