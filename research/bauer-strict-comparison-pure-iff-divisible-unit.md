---
rg: 2
id: bauer-strict-comparison-pure-iff-divisible-unit
kind: claim
title: On a Bauer trace simplex, a strict-comparison algebra is pure iff its unit is almost divisible
distinct_from:
  rank-density-and-strict-comparison-give-purity: that derives purity from rank density of every continuous profile on any simplex; this shows that on Bauer simplices almost divisibility of the single class [1] already suffices.
  stw99-problem-xxvii-comparison-vs-divisibility: that asks whether strict comparison gives purity in general; this proves that on Bauer simplices the question is equivalent to almost divisibility of the unit.
  toms-winter-bauer-tlfnd-iff-tracially-divisible-unit: that concludes Z-stability and needs nuclearity and tracially locally finite nuclear dimension; this concludes purity for exact algebras with no dimension hypothesis.
  strict-comparison-unit-divisibility-equivalences: that relates the ways a unit can divide on any simplex; this adds purity and rank density to the list, using the Bauer property.
artifacts:
  - research/artifacts/ex-toms-winter-unit-divisibility-equivalences-2026-09-12.md
  - research/artifacts/ex-toms-winter-bauer-divisible-unit-2026-09-12.md
---

**Theorem.** Let `A` be a unital, simple, separable, exact, non-elementary
C*-algebra whose trace simplex is a nonempty Bauer simplex, with strict comparison
of positive elements. These are equivalent:
- (a) `A` is pure (almost unperforated and almost divisible Cuntz semigroup);
- (b) rank density: every continuous strictly positive affine function on `T(A)` is
  a uniform limit of rank functions;
- (c) bounded rank density (RD_b);
- (d) for every `n` some `x ∈ W(A)` has `n x ≤ [1_A] ≤ (n+1) x`;
- (e) the unit is tracially `N`-divisible for every `N`;
- (f) for every `n ≥ 2` there is a unital `*`-homomorphism `Z_{n,n+1} → A`.

So on Bauer simplices, part (1) of STW XXVII is a question about one element. A
strict-comparison algebra with Bauer simplex that is not pure has an almost
indivisible unit: for some `n`, no `x ∈ W(A)` satisfies `n x ≤ [1] ≤ (n+1) x`. It
contains no unital `Z_{n,n+1}` for that `n`, and no unital simple
infinite-dimensional unique-trace subalgebra.

No nuclearity or dimension hypothesis is used. With nuclearity and locally finite
nuclear dimension, (a) is Z-stability (Winter).

**Proof** (route `bauer-strict-comparison-pure-iff-divisible-unit-proof`).
- (e) ⟹ (c): central step functions.
- (c) ⟹ (b): spectral estimates.
- (b) ⟹ (a): the established purity theorem.
- (a) ⟹ (d): almost divisibility at the compact class `[1]`.
- (d) ⟺ (e) ⟺ (f): `strict-comparison-unit-divisibility-equivalences`.

Not reviewed. No novelty asserted.
