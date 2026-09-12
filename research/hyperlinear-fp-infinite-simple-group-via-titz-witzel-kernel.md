---
rg: 2
id: hyperlinear-fp-infinite-simple-group-via-titz-witzel-kernel
kind: route
title: A sofic smallest Titz--Witzel kernel is a torsion-free sofic finitely presented simple hyperlinear group
target: hyperlinear-fp-infinite-simple-group
requires:
  - titz-witzel-kernel-sofic
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
  - sofic-implies-hyperlinear
---

Let `K = Gamma_1^2`.  By `titz-witzel-simple-kazhdan-cat0-lattices-exist`,
`K` is finitely presented, infinite, simple and torsion-free.  If `K` is
sofic, `sofic-implies-hyperlinear` makes it hyperlinear.  That meets the root
with both preferred strengthenings, torsion-free and sofic.

The route waits entirely on `titz-witzel-kernel-sofic`, whose gate is the
finite permutation problem in `titz-witzel-soficity-is-one-finite-csp`.  It
is independent of the amenable-edge splitting route: `K` is Kazhdan, hence
has property `FA` and no splitting.
