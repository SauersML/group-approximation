---
rg: 2
id: random-complex-cheeger-capped-via-detecting-quotient
kind: route
title: Detecting quotients cap the random cocycle Cheeger constant at the inverse triangle count
target: random-complex-cheeger-capped-by-triangle-count
requires: [finite-quotient-caps-cocycle-cheeger-constant, random-complex-mid-range-pair-properties, random-complex-missing-triangle-detected-by-quotient]
---

## Why sufficient

Fix `η` and `λ = 1/4`, and sample `(Y, Z, Δ)` as usual.

* A.a.s. `Y` is a `1/4`-local spectral expander, `|Y(2)| = (1+o(1)) p C(n,3)`,
  and a finite quotient of `π_1(Y)` detects the perimeter of `Δ`.
* The cap then gives `h_1(Z,Sym) <= 3/|Y(2)| = O(n^(-3)p^(-1))`.
* The total-variation transfer moves this a.a.s. property from `Z` to
  `Y(n,p)`, and it holds for every `η`.
