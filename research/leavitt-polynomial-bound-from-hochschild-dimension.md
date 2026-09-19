---
rg: 2
id: leavitt-polynomial-bound-from-hochschild-dimension
kind: route
title: L_k(1,2) has Hochschild dimension one, so the fraction-field Koszul lower bound allows at most one commuting independent element
target: leavitt-algebras-contain-no-two-variable-polynomial-ring
requires: [hochschild-dimension-bounds-commuting-independent-families, leavitt-algebra-hochschild-dimension-at-most-one]
---

Let `k` be a field and `L = L_k(1,2)`.

1. By `leavitt-algebra-hochschild-dimension-at-most-one`, `pd_(L^e) L <= 1`.
2. By `hochschild-dimension-bounds-commuting-independent-families` with `d = 1` and `r = 1`, `L` has no commuting
   independent family of size `2`.
3. So if `a, b ∈ L` commute, then `P(a, b) = 0` for some nonzero `P ∈ k[x, y]`. By Section 4 of
   `polynomial-subring-flat-dimension-via-fraction-field-koszul`, `k[x, y]` has no injective algebra map into
   `L`, unital or not. ∎

The same argument, with general `r`, excludes `k[x, y]` from every `M_r(L)`.

**Independent cross-check of the upper bound.** `L ⊗_k K = L_K(1,2)` for every field `K ⊇ k`. Leavitt path
algebras over a field are hereditary (Ara--Moreno--Pardo, *Nonstable K-theory for graph algebras*, Algebr.
Represent. Theory 10 (2007), which proves `L_K(E)` hereditary for row-finite `E`; the theorem number was not
re-checked for this note). So `l.gl.dim(L ⊗ k(y_1, y_2)) <= 1` also follows from the
literature, without the bimodule resolution. Only this inequality enters Section 3 of the route
`commuting-rank-from-bimodule-resolution-and-koszul`.

**What the route bypasses.** The earlier decomposition `leavitt-rank-one-from-free-field-matrices-and-degree-reduction`
went through the grading half, `leavitt-polynomial-pairs-move-to-the-nonnegative-part`, and through
matrices over the free field. This route needs neither. The lower bound
`polynomial-subrings-bound-transcendental-flat-dimension` asks nothing of `L` as a module over `k[a, b]`. This
removes the flatness gate recorded in `leavitt-algebras-have-no-trdeg-two-subfields` and
`leavitt-polynomial-pairs-contain-a-universally-singular-element`.
