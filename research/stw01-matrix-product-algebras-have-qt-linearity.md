---
rg: 2
id: stw01-matrix-product-algebras-have-qt-linearity
kind: claim
title: Every bounded quasitrace on a product of matrix algebras, or on any quotient of one, is a trace
distinct_from:
  stw01-hyperfinite-factor-already-has-qt-linearity: that imports the Murray--von Neumann additivity theorem for the II_1 factor R; this proves quasitrace linearity for arbitrary l-infinity products of full matrix algebras and all their quotients, including norm ultraproducts of matrix algebras, by an elementary balancing argument.
artifacts:
  - research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md
---

For any family of matrix algebras `M_(n_i)`, `i in I`, every bounded
2-quasitrace on `W = prod_i M_(n_i)` is a trace, and so is every bounded
2-quasitrace on every quotient of `W`.  In particular this holds for every norm
ultraproduct `prod_omega M_(n_k)`, which is not exact when `n_k -> infinity`.

The quasitrace factors through the center-valued trace
`T(x) = (tr_(n_i)(x_i) 1)_i`, which is linear.  The key step is that a mean-zero
diagonal block with entries bounded by `M` is `w - v w v*` for one block
permutation unitary `v` and a diagonal `w` with norm at most `M`.  To see this,
order the entries so that the running sums stay in `[-M, M]` and take `w` to be
the running sums with a cyclic shift.

This supplies the input replacing "quasitraces on finite-dimensional algebras
are traces" when approximations are taken coordinatewise in a product of
algebras.  See `stw01-bounded-nuclear-dimension-products-qt-linearity`.
