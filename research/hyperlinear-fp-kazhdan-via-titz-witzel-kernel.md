---
rg: 2
id: hyperlinear-fp-kazhdan-via-titz-witzel-kernel
kind: route
title: A sofic smallest Titz--Witzel kernel is a finitely presented simple Kazhdan sofic group
target: hyperlinear-fp-infinite-simple-kazhdan-group
requires: [titz-witzel-kernel-sofic, titz-witzel-simple-kazhdan-cat0-lattices-exist, sofic-implies-hyperlinear]
---

Let `K = Gamma_1^2`.
- By `titz-witzel-simple-kazhdan-cat0-lattices-exist`, `K` is finitely presented, infinite,
  simple and Kazhdan. It is also torsion-free and CAT(0).
- If `K` is sofic (`titz-witzel-kernel-sofic`), it meets the target in its preferred sofic form,
  and `sofic-implies-hyperlinear` gives the hyperlinear form.

The route waits on the three-permutation gate `titz-witzel-soficity-is-one-finite-csp`. By
`vcd-two-groups-contain-no-kazhdan-commuting-pairs`, no compression or lamp certificate can refute
it.
