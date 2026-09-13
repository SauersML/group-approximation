---
rg: 2
id: bauer-strict-comparison-unit-division-is-local
kind: claim
title: Under strict comparison on a Bauer simplex, the unit divides as soon as it divides over a neighbourhood of every extreme trace
distinct_from:
  bauer-gamma-failure-localizes-to-infinite-dim-point: that localizes failure of central halving of the hyperfinite W*-bundle to infinite-dimensional points, with no comparison hypothesis; this localizes failure of non-central division of the unit under strict comparison.
  bauer-c-space-strict-comparison-divides-unit: that proves division when the whole boundary has property C, by screening with summable precisions; this is the local-to-global principle with no dimension hypothesis, where precisions are fixed after the cover.
artifacts:
  - research/artifacts/ex-tw-c-space-unit-division-part2-2026-09-13.md
---

**Theorem.** Let `A` be a unital, simple, separable, exact, non-elementary
C*-algebra with strict comparison and nonempty Bauer simplex, `K = ∂_e T(A)`.
- Say the unit *divides over* a closed `Y ⊆ K` if for every `N` and `δ > 0` some
  c.p.c. order zero `φ: M_N → A` has `λ(1 − φ(1)) < δ` for all `λ ∈ Y`.
- If every `λ ∈ K` has a closed neighbourhood over which the unit divides, then the
  unit is tracially `N`-divisible for every `N`.

**Consequence.** Suppose such an `A` has an indivisible unit. Then its *division locus*
(the points of `K` with no closed neighbourhood over which the unit divides) is a
nonempty closed set.

**Proof** (Proposition D of the part 2 artifact).
1. Finitely many interiors `int Y_1, …, int Y_L` cover `K`.
2. Run the construction of `bauer-c-space-strict-comparison-divides-unit` with one level
   per `Y_k`, and a partition of unity with `supp h_k ⊆ int Y_k`.
3. Since `L` is fixed first, one precision `(N, δ)` with
   `L(6(1/(4N) + δ)^{1/2} + δ) ≤ ε/2` serves every level.
4. Staircases, orthogonalizing moves and the final rank estimate apply verbatim. ∎

Not reviewed.

**Open refinement.** Does the division locus contain no point with a closed
neighbourhood that has property C? Over a closed C-space `Y`, the construction gives
elements whose rank is close to `t` near `Y`. It does not give order zero maps that are
good on `Y`, and a local form of Rørdam–Winter's Proposition 5.1 is missing.
