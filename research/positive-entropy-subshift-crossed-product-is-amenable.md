---
rg: 2
id: positive-entropy-subshift-crossed-product-is-amenable
kind: claim
title: Is the crossed product of a positive-entropy minimal subshift algebraically amenable?
---

**OPEN.** Let `X ⊆ A^Z` be an infinite minimal subshift of **positive** topological entropy `h > 0` and
`R = LC(X, k) ⋊_T Z`. Is `R` amenable in Elek's sense?

**Why it is the boundary of the amenability route.** `R` always has exact matricial models by return-word
towers, so it always has a rank model and its Kazhdan elementary groups are LEF. The amenability route of
`simple-amenable-affine-algebras-have-unital-rank-models` reaches it only through subexponential growth
(`zero-entropy-subshift-pestov-ring-has-rank-model-by-growth`), which fails here: complexity grows like
`e^{hn}`, so `R` has exponential growth. A positive answer would say algebraic amenability still covers the
whole minimal `Z` family; a negative answer would show the amenable class is a **proper** subclass of the
matricial class, so that amenability is a genuinely different condition from the measure side rather than a
reformulation of it.

Either answer sharpens rung (Σ) of `kazhdan-elementary-approximation-type-mirrors-ring-type`. A negative
answer is the more informative one, since it would exhibit a simple affine algebra that is stably finite and
has a rank model yet is not amenable, refuting any attempt to make amenability the measure-side criterion.

## Attempts

- **Product Følner subspaces die at positive entropy.** Try `Q = A_m ⊗ span{u^j : |j| ≤ n}`, where `A_m` is
  the (finite dimensional, and a subalgebra) space of functions on the window `[−m, m]`. For
  `B` spanned by `A_l` and `u^{±J}`, the identity `(f u^i)(b u^j) = f·(b ∘ T^{-i})·u^{i+j}` gives
  `BQ ⊆ A_(m+J) ⊗ span{u^x : |x| ≤ n+J}`, so
  `dim(BQ)/dim(Q) ≤ [dim A_(m+J)/dim A_m]·[(2n+2J+1)/(2n+1)]`.
  The second factor tends to `1` as `n → ∞`. The first is `p(2m+2J+1)/p(2m+1)`, which tends to `e^{2hJ} > 1`
  for every `m` when `h > 0`. So no product subspace works, for any choice of `m` and `n`.
- **Local finiteness alone is not enough.** `LC(X,k)` is locally finite, hence amenable on its own, and `Z`
  is amenable; the attempt above shows that these two facts do not combine, because no finite dimensional
  subalgebra of `LC(X,k)` is close to shift-invariant when entropy is positive. So the natural "locally
  finite by amenable group implies amenable" statement is **not** available, and must not be assumed.
- **Not settled by Elek's Tarski alternative.** Elek's equivalence amenable ⟺ not paradoxical is stated only
  for affine algebras *without zero divisors*; `R` has idempotents, so the alternative gives nothing here.
- **Not settled by stable finiteness.** `R` is stably finite (it has a rank model), and Elek's implications
  run from amenability to stable finiteness, not back.
