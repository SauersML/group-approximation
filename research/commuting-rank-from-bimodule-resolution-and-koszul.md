---
rg: 2
id: commuting-rank-from-bimodule-resolution-and-koszul
kind: route
title: Tensor the length-d bimodule resolution with a module for gl.dim(A ⊗ K) <= d, and compare with the fraction-field Koszul lower bound n <= gl.dim(A ⊗ K)
target: hochschild-dimension-bounds-commuting-independent-families
requires: [polynomial-subrings-bound-transcendental-flat-dimension]
---

All unmarked tensor products are over `k`.

## 1. Upper bound: `l.gl.dim(A ⊗ K) <= d` for every field extension `K ⊇ k`

Fix a resolution `0 -> P_d -> ... -> P_0 -> A -> 0` by projective `A^e`-modules. Let `M` be a left
`A ⊗ K`-module, that is, an `A`-module with a commuting `K`-action.

- **Exactness.** Each `P_j` is projective as a right `A`-module, because `A^e = A ⊗ A^op` is free as a right
  `A`-module. `A` is projective too. So the resolution splits as right `A`-modules, and
  `0 -> P_d ⊗_A M -> ... -> P_0 ⊗_A M -> M -> 0` stays exact.
- **Module structure.** `A` acts through the left action on `P_j`, and `K` acts on `M`. The maps are
  `A ⊗ K`-linear, and `A ⊗_A M = M`.
- **Projectivity.** `A^e ⊗_A M ≅ A ⊗ M ≅ (A ⊗ K) ⊗_K M`. This is a free `A ⊗ K`-module, since `M` is free over
  the field `K`. Direct sums and summands follow, so each `P_j ⊗_A M` is projective.

So `pd M <= d` for every `M`, which gives `l.gl.dim(A ⊗ K) <= d`, and so `w.gl.dim(A ⊗ K) <= d`.

## 2. Matrix rings

`M_r(A) ⊗ K ≅ M_r(A ⊗ K)`. Left global dimension is Morita invariant: `N ↦ (A ⊗ K)^r ⊗_(A⊗K) N` is an
equivalence of module categories (Lam, *Lectures on Modules and Rings*, §17–18), and an equivalence preserves
exact sequences and projective objects. Hence `l.gl.dim(M_r(A) ⊗ K) <= d`.

## 3. Conclusion

Suppose `M_r(A)` has a commuting independent family of size `n`. Apply
`polynomial-subrings-bound-transcendental-flat-dimension` to the `k`-algebra `M_r(A)` with
`K = k(y_1, ..., y_n)`. This gives `n <= l.gl.dim(M_r(A) ⊗ K) <= d`. So `n <= d`.

The statement about non-unital maps is Section 4 of `polynomial-subring-flat-dimension-via-fraction-field-koszul`. ∎

**Remark.** Only `gl.dim(A ⊗ k(y_1, ..., y_n)) <= d` was used. So the bound `n <= d` holds for any algebra with
that property, whether or not its Hochschild dimension is finite.
