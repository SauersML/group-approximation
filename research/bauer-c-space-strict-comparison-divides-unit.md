---
rg: 2
id: bauer-c-space-strict-comparison-divides-unit
kind: claim
title: With a Bauer trace simplex whose extreme boundary has property C, strict comparison makes the unit tracially divisible
distinct_from:
  strict-comparison-forces-tracially-divisible-unit: that is the crux on every trace simplex; this proves it when the simplex is Bauer and its extreme boundary has Haver's property C, for exact algebras.
  bauer-tracially-divisible-unit-gives-bounded-rank-density: that assumes a divided unit and produces every continuous profile; this produces the divided unit from strict comparison and property C.
  stw22-c-space-screening-from-local-lifts: that screens local weighted lifts by property C to kill traces on fibre gaps of completions of C(X) ⊗ U, conditionally on local lifting; this uses the same summable screening, with strict comparison moves, to divide the unit of a simple algebra, unconditionally.
  stw18-finite-trace-boundary-toms-winter: that gives Z-stability for nuclear algebras with compact finite-dimensional boundary; this divides the unit of exact algebras over every C-space boundary.
  r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial: that is central triviality of hyperfinite W*-bundles over countable unions of closed finite-dimensional compacta, with no comparison; this is non-central division of the unit over C-spaces under strict comparison.
artifacts:
  - research/artifacts/ex-tw-c-space-unit-division-2026-09-13.md
  - research/artifacts/ex-tw-c-space-unit-division-part2-2026-09-13.md
---

**Theorem.** Let `A` be a unital, simple, separable, exact, non-elementary
C*-algebra with strict comparison of positive elements. Suppose `T(A)` is a nonempty
Bauer simplex and `K = ∂_e T(A)` has Haver's property C.
- Property C: for every sequence of open covers `U_k` there are disjoint open families
  `V_k` refining `U_k` with `⋃_k V_k` covering `K`.

Then for every `N` and `ε > 0` there is a c.p.c. order zero map `φ: M_N → A` with
`τ(φ(1)) > 1 − ε` for every `τ ∈ T(A)`.

**Proof architecture** (route `bauer-c-space-strict-comparison-divides-unit-proof`).
1. **Local division.** Near every extreme trace, matrix units of the fibre II_1 factor
   lift to an order zero `M_N → A` that is `δ`-good on a neighbourhood.
2. **Screening.** Property C, applied to the covers at precisions `(N_k, δ_k)` with
   `Σ_k (1/(4N_k) + δ_k)^{1/2}` small, gives finitely many levels. Each level is a
   disjoint family, and its local maps combine through Ozawa's central `C(K)`.
3. **Staircases.** One central staircase per level, over its `N_k` pieces, gives a
   global element of rank `t h_k ± O((1/N_k + δ_k)^{1/2})` where it is active and
   nearly `0` elsewhere. Here `(h_k)` is a partition of unity.
4. **Orthogonalizing moves.** Strict comparison and Rørdam's lemma move each level's
   piece into the exact orthogonal complement of the earlier pieces. The rank margin
   is at least `1 − t − ε`. Ranks add exactly over orthogonal sums, so errors do not
   compound.
5. **Division.** The sum has rank within `γ` of `t` at every trace, with
   `(t − γ, t + γ) = (1/(n+1), 1/n)`. So `n[x] ≤ [1] ≤ (n+1)[x]` for every `n`, and
   `strict-comparison-unit-divisibility-equivalences` divides the unit.

**What it gives.** `bauer-c-space-strict-comparison-pure-and-z-stable`: purity, and
`Z`-stability under nuclearity and tlfnd, on this locus. Relative to the graph, this is
new beyond countable unions of closed finite-dimensional compacta, or for non-nuclear
exact algebras.

**Model test.**
- `C([0,1])`: the conclusion fails, and the algebra is not simple.
- Toms's no-Gamma AH algebra: its simplex is Poulsen, not Bauer, and it fails strict
  comparison. The hypothesis fails.
- Every `Z`-stable algebra with Bauer simplex satisfies the conclusion.
- Over the Hilbert cube, property C fails and the theorem says nothing.

Not reviewed. Novelty check bounded: repository literature notes only, web search
unavailable this session.
