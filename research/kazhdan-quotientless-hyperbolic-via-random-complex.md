---
rg: 2
id: kazhdan-quotientless-hyperbolic-via-random-complex
kind: route
title: A mid-range random complex group without large finite quotients is a quotientless hyperbolic Kazhdan group
target: kazhdan-hyperbolic-group-without-finite-quotients
requires: [random-complex-mid-range-pair-properties, meshulam-random-complex-no-polynomial-quotients, random-complex-group-no-large-finite-quotients]
---

## Why sufficient

Fix `η` and `c` from the open premise, `p = n^(-1+η)`, and `λ = 1/4`.

* A.a.s. `π_1(Y)` is hyperbolic and nontrivial, and `Y` is a `1/4`-local spectral
  expander (`random-complex-mid-range-pair-properties`). By the Garland--Żuk
  spectral criterion (links with spectral gap above `1/2`; Ballmann--Świątkowski,
  Żuk 2003), `π_1(Y)` has property (T).
* Meshulam excludes nontrivial quotients of order at most `n^c`, and the premise
  excludes all larger ones.
* A nontrivial group with no nontrivial finite quotient is infinite. So some
  sample is an infinite hyperbolic Kazhdan group with no nontrivial finite quotient.

This is the Linial--Meshulam instance of the "random groups" attempt recorded on
the target. The premise concerns only the large-quotient regime, because
Meshulam's counting removes every quotient of polynomial order.
