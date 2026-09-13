---
rg: 2
id: toms-winter-bauer-tlfnd-iff-tracially-divisible-unit
kind: claim
title: With a Bauer trace simplex, tlfnd and strict comparison, Z-stability is equivalent to tracial divisibility of the unit
distinct_from:
  toms-winter-holds-on-tlfnd-rank-density-locus: that proves Z-stability from strict comparison, tlfnd and bounded rank density on any simplex; this shows that on Bauer simplices bounded rank density reduces to divisibility of the unit, and records the equivalence with Z-stability.
  nontrivial-w-star-bundle-with-r-fibres-exists: that asks for a nontrivial hyperfinite W*-bundle with no C*-algebra and no comparison; this says that a strict-comparison counterexample on this locus has a bundle with no uniform tracial halving of the unit at all, central or not.
  stw99-problem-lxv-jiang-su-embeddings: that asks which unital algebras contain a unital Z; this shows that for strict-comparison algebras on this locus a unital Z, or any unital simple infinite-dimensional unique-trace subalgebra, already forces Z-stability.
  bauer-gamma-failure-localizes-to-infinite-dim-point: that confines Gamma failure on Bauer simplices to locally infinite-dimensional extreme traces; this shows that with strict comparison and tlfnd, Gamma failure is failure of tracial divisibility of the unit.
artifacts:
  - research/artifacts/ex-toms-winter-bauer-divisible-unit-2026-09-12.md
  - research/artifacts/ex-toms-winter-bauer-divisible-unit-part2-2026-09-12.md
---

**Theorem.** Let `A` be a unital, simple, separable, nuclear, non-elementary
C*-algebra whose trace simplex is a nonempty Bauer simplex. Suppose `A` has
tracially locally finite nuclear dimension (Vaccaro, arXiv:2604.24682,
Definition 1.5) and strict comparison of positive elements. These are equivalent:
- (a) `A ≅ A ⊗ Z`;
- (b) `A` has uniform property Gamma;
- (c) bounded rank density (RD_b);
- (d) for every `N`, a unital `*`-homomorphism `M_N → A^U`;
- (e) the unit of `A` is tracially `N`-divisible for arbitrarily large `N`: for
  every `ε > 0` some c.p.c. order zero `φ: M_N → A` has `τ(φ(1)) > 1 − ε` at every
  trace.

**Shape of a counterexample.** A unital Toms–Winter counterexample on this locus
has a tracially indivisible unit.
- For all large `N` there is `ε_N > 0` such that every c.p.c. order zero
  `φ: M_N → A` has `τ(φ(1)) ≤ 1 − ε_N` at some trace.
- Its tracial ultrapower has no projection of constant trace `1/N` for large `N`.
- `A` contains no unital simple infinite-dimensional C*-subalgebra with a unique
  trace, such as `Z`, a UHF algebra or an irrational rotation algebra.
- `A` admits no unital `*`-homomorphism from `Z_{n,n+1}` for large `n`.

**On the hypotheses.** Locally finite nuclear dimension implies the tracial
version, and Vaccaro records that no nuclear algebra without locally finite nuclear
dimension is known. So among known nuclear algebras this is the Bauer-simplex case
of Toms–Winter.

**Proof** (Section 2 of the first artifact, Section 3 of part 2).
- (e) ⟹ (c): `bauer-tracially-divisible-unit-gives-bounded-rank-density`.
- (c) ⟹ (b), in four steps:
  1. strict comparison gives projection comparison in the ultrapower;
  2. comparison and RD_b divide projections;
  3. strict comparison and RD_b give tracial support projections;
  4. support projections, division and tlfnd give uniform Gamma.
- (b) ⟹ (a): CETW Theorem A.
- (a) ⟹ (d): tracially large order zero maps `M_N → Z`, transported through
  `A ⊗ Z ≅ A`.
- Unique-trace subalgebras, and `Z_{n,n+1}` with `n` large, give (e) directly.

Not reviewed.
