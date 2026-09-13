---
rg: 2
id: cantor-crossed-product-mixed-via-finite-type-persistence
kind: route
title: Persistence of finite clopen classes turns the measure-free topologically free finite-type actions into mixed crossed products
target: cantor-crossed-product-with-finite-type-is-mixed
requires:
  - finite-clopen-type-stays-finite-in-cantor-crossed-product
  - topologically-free-minimal-cantor-action-with-finite-clopen-type
  - kmp-plain-paradox-groupoid-dichotomy
---

Take the action of `topologically-free-minimal-cantor-action-with-finite-clopen-type`
(Boldrini--Prasad, arXiv:2607.01896, Corollary 6.12, first): minimal,
topologically free, no invariant probability measure, and a nonempty clopen
`U` with `[1_U]` finite.  Let `A = C(X) rtimes_r Gamma`, which is simple.

* By `finite-clopen-type-stays-finite-in-cantor-crossed-product`, `1_U` is a
  finite projection, so `A` is not purely infinite.
* There is no invariant measure, so by KMP Theorem 6.5
  (`kmp-plain-paradox-groupoid-dichotomy`) `A` is not stably finite.

So `A` is neither stably finite nor purely infinite, which is the target.
