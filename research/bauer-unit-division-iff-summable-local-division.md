---
rg: 2
id: bauer-unit-division-iff-summable-local-division
kind: claim
title: Under strict comparison on a Bauer simplex, the unit divides iff the extreme boundary is summably divisible, and failure lives in the C-kernel
distinct_from:
  bauer-c-space-strict-comparison-divides-unit: that proves division when the whole boundary has property C; this characterizes division on every compact boundary and confines failure to a closed locus with no relative C-neighbourhoods.
  bauer-strict-comparison-unit-division-is-local: that is local-to-global with a single precision per neighbourhood; this weights local divisions of different precisions and gives an exact characterization.
  bauer-gamma-failure-localizes-to-infinite-dim-point: that confines failure of central halving of the hyperfinite W*-bundle to infinite-dimensional points, with no comparison hypothesis; this confines failure of non-central division of the unit under strict comparison to the C-kernel of the boundary.
artifacts:
  - research/artifacts/ex-tw-c-space-unit-division-part3-2026-09-13.md
  - research/artifacts/ex-tw-c-space-unit-division-part2-2026-09-13.md
---

**Setting.** `A` is unital, simple, separable, exact and non-elementary, with strict
comparison. `T(A)` is a nonempty Bauer simplex with extreme boundary `K`.

**Definitions.**
- A *division set* `(O, φ, N, δ)` is an open `O ⊆ K` and a c.p.c. order zero
  `φ: M_N → A` with `λ(1 − φ(1)) < δ` on `O`. Its weight is `ω = (1/N + δ)^{1/2}`.
- A finite family of division sets is *ε-summable* if the weights of the members
  containing any given point sum to at most `ε`.
- `Y ⊆ K` is *summably divisible* if every `ε > 0` admits an ε-summable family covering `Y`.
- `Z_sum(A)` is the set of points with no summably divisible closed neighbourhood.

**Theorem.**
- (a) The unit is tracially `N`-divisible for every `N` iff `K` is summably divisible.
- (b) `Z_sum(A)` is closed, and it is empty iff the unit divides.
- (c) Every closed `Y ⊆ K` with Haver's property C is summably divisible.
- (d) No point of `Z_sum(A)` has a closed neighbourhood in `Z_sum(A)` with property C.
  Hence `Z_sum(A)` lies in the C-kernel of `K`, the stable value of the transfinite
  sequence of sets of points without closed C-neighbourhoods.

**Consequences.**
- `bauer-c-space-strict-comparison-divides-unit` is the case `Y = K` of (c) and (a).
- `bauer-strict-comparison-unit-division-is-local` is the single-precision case of (b).
- A strict-comparison algebra on a Bauer simplex with an indivisible unit has:
  - a nonempty closed locus in which no point has a C-neighbourhood;
  - some `ε > 0` such that every finite cover of `K` by division sets has a point where
    the weights exceed `ε`.

**Proof** (route `bauer-unit-division-iff-summable-local-division-proof`; part 3 artifact).
- (a) is Section 3 of part 2, with one level per division set.
- (b) and (d) are compactness arguments. Summable families for finitely many sets
  combine with `ε/m`.
- (c) is property C screening at precisions `ω_k = ε 2^{−k}`. Disjoint separating
  neighbourhoods keep one set per level at every point.

**Model test.**
- For `C(K)`, order zero maps `M_N → C(K)` with `N ≥ 2` vanish. So every division set has
  `ω ≥ 1`, and `K` is not summably divisible; `C(K)` is not simple.
- A `Z`-stable algebra has `K` itself as a division set at every precision.

Not reviewed.
