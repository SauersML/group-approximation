---
rg: 2
id: leavitt-polynomial-rank-one-via-hochschild-dimension
kind: route
title: L_k(1,2) is quasi-free, and quasi-free algebras contain no two-variable polynomial ring
target: leavitt-algebras-contain-no-two-variable-polynomial-ring
requires: [polynomial-rank-is-at-most-hochschild-dimension, leavitt-algebra-hochschild-dimension-at-most-one]
---

Let `k` be any field and `L = L_k(1,2)`.

1. By `leavitt-algebra-hochschild-dimension-at-most-one`, `hd_k(L) <= 1`, for every
   field `k`.
2. By `polynomial-rank-is-at-most-hochschild-dimension` with `d = 1`, `L` has no two
   commuting algebraically independent elements.

That is the target, for every field at once. The route avoids the grading step
`leavitt-polynomial-pairs-move-to-the-nonnegative-part` and the free-field input of the
older route `leavitt-rank-one-from-free-field-matrices-and-degree-reduction`.

**Corollary: Ara--Cortiñas Question 5.7 is negative over every field.**
arXiv:1108.0352v3, p. 8, asks whether there is a unital homomorphism
`L_2 ⊗ L_2 -> L_2`. There is not even a nonzero one.
- `L ⊗_k L` is simple, because `L` is central simple. So a nonzero homomorphism is
  injective.
- `L` is `Z`-graded with `x_1` of degree `1` and `x_1^* x_1 = 1`, so the powers
  `x_1^m` are nonzero homogeneous elements of distinct degrees. Hence
  `k[x_1] ≅ k[t]`, and `L ⊗ L ⊇ k[x_1] ⊗ k[x_1] ≅ k[s, t]`.
- An injective image of that, unital or not (last paragraph of
  `polynomial-rank-hochschild-bound-via-diagonal-koszul`), is a two-variable polynomial
  ring in `L`, which is excluded.

The graph's consumer `no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`
is the case `k = F_2`.
