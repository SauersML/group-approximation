---
rg: 2
id: stw18-k1-witness-constraints
kind: claim
title: Any strict-comparison counterexample to K1-injectivity has stable rank two, a rank gap and a wild trace simplex
distinct_from:
  stw18-k1-witness-strict-comparison-not-k1-injective: that asks for the witness; this proves what any witness must satisfy.
  strict-comparison-rank-surjectivity-forces-sr1: that is Lin's general theorem; this assembles it with Rieffel, Toms, Jiang, Toms--White--Winter and Lin's condition (C) into the complete constraint list for a witness.
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

Let `A` be simple, separable, unital, nuclear and non-elementary, with strict
comparison of positive elements with respect to a nonempty trace simplex. If
`A` is not K1-injective, then:

1. `A` is not purely infinite and is stably finite;
2. `sr(A) >= 2`;
3. the rank map `Gamma: Cu(A) -> LAff_+(QT~(A))` is not surjective, so not
   all ranks occur, tracial approximate oscillation zero fails, and `A` is not
   pure;
4. `A` is not an AH algebra;
5. `A` is not Z-stable;
6. the extreme tracial boundary is not compact finite-dimensional, and the
   tracial cone has no basis satisfying Lin's condition (C);
7. `A` refutes both STW Problem XVIII and STW Problem XXIII;
8. `A` is not a crossed product `C(X) ⋊ Gamma` of a free minimal action with the
   uniform Rokhlin property; in particular it is not any free minimal
   `C(X) ⋊ Z^d`;
9. in every presentation of `A` as a unital injective inductive limit, all
   but finitely many stages fail K1-injectivity.
