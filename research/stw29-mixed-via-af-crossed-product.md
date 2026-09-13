---
rg: 2
id: stw29-mixed-via-af-crossed-product
kind: route
title: A real rank zero crossed product that is neither stably finite nor purely infinite has a matrix algebra containing a finite and an infinite projection
target: stw29-rr0-mixed-simple-algebra-exists
requires: [stw29-mixed-rr0-af-crossed-product-exists]
---

Let `A = D rtimes_lambda Gamma` be as in `stw29-mixed-rr0-af-crossed-product-exists`.
It is simple because the action is minimal and properly outer
(Olesen--Pedersen, Theorem 7.2, as invoked in Rainone's proof of Theorem 4.16).

* `A` is not stably finite, so some `M_n(A)` contains an infinite projection.
* `A` has real rank zero and is not purely infinite, so some nonzero
  hereditary subalgebra of `A` contains no infinite projection.  Real rank zero
  gives it a nonzero projection `p`, which is finite.  So `p direct_sum 0` is a
  nonzero finite projection in `M_n(A)`.
* `M_n(A)` is simple with real rank zero.

So `M_n(A)` witnesses `stw29-rr0-mixed-simple-algebra-exists`.
