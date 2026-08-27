---
rg: 2
id: bounded-involutive-cayley-expander-proof
kind: route
title: Factor uniform simple-group expander generators into four involutions
target: bounded-involutive-cayley-expanders-for-sl-n-two
requires: []
---

Take the absolute-size, absolute-gap generating sets for the simple groups
`SL_n(2)` from the finite-simple-group expander theorem.  By the uniform
involution-width theorem, factor each generator into at most four
involutions and take the multiset of every factor.  It still generates.
For each factorization, telescope the displacement and apply Cauchy--Schwarz
to obtain `(BIC1)`.  Averaging over the old bounded set and then over at most
four times as many new factors loses at most a factor sixteen in the
Poincare constant.  The resulting involutive Cayley sets have absolute size
and absolute gap.
