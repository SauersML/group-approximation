---
rg: 2
id: o2-ideal-projection-unit-witness-fails-cancellation
kind: claim
title: An O_2-multiplier ideal with a full projection approximate unit and order cancellation has K1-injective unitization
distinct_from:
  o2-ideal-finite-nucdim-counterexample-unital-quotients: that constrains witnesses of finite nuclear dimension through Robert's stability theorem; this constrains projection-rich witnesses of any nuclear dimension through cancellation.
artifacts:
  - research/artifacts/k1-o2-ideal-finite-nuclear-dimension-2026-09-13.md
---

Let `I` be σ-unital, with an increasing approximate unit of projections `p_n`, each full in `I`.

1. Suppose that for all `n, k` some `m` has `p_n^{⊕k} ≲ p_m - p_n`. Then `Ĩ` is K1-injective.
2. Suppose `M(I)` contains `O_2` unitally, and the Murray--von Neumann monoid of `I` has order cancellation:
   `[a] + [p] >= [b] + [p]` implies `[a] >= [b]`. Then the hypothesis of item 1 holds, so `Ĩ` is K1-injective.

The halving words give `2^j[p_n] <= [p_m]` for large `m`. Cancellation turns this into room for
`2^j - 1` copies of `p_n` inside `p_m - p_n`. There the K1-null-homotopy of the compressed witness can be
transported back, using Brown's full-corner isomorphism on `K_1`.

So a witness for `o2-multiplier-ideal-with-non-k1-injective-unitization` is of one of two kinds. Either it
has no approximate unit of full projections, like the projectionless `C_0(Y) ⊗ D` models. Or its projection
monoid fails order cancellation at every scale, as in Villadsen's second-type algebras. Simple witnesses
also have infinite nuclear dimension (artifact, Corollary 5).
