---
rg: 2
id: unique-product-non-sofic-from-left-orderable
kind: route
title: A left-orderable nonsofic group has unique products
target: unique-product-non-sofic-group
requires: [left-orderable-non-sofic-group]
---

Let `W` be left-orderable and nonsofic, with left-invariant order `<`.  Let
`A, B` be finite nonempty subsets.

- Put `b_max = max B`.  For each `a in A` and `b in B`, left invariance gives
  `a b <= a b_max`.
- Let `c = max_(a in A) a b_max = a_0 b_max`.
- Suppose `c = a' b'` with `a' in A` and `b' in B`.  Then
  `c = a' b' <= a' b_max <= c`, so `a' b' = a' b_max`.
- Left cancellation gives `b' = b_max`, and then `a' = a_0`.

So `c` has a unique expression, and `W` has unique products.  ∎
