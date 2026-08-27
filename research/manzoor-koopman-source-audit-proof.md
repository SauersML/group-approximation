---
rg: 2
id: manzoor-koopman-source-audit-proof
kind: route
title: Pull back along the stabilizer map and decompose the labeled Schreier realization
target: manzoor-cdi-source-has-no-determined-koopman-gate
requires:
  - group-basis-actions-have-permutation-koopman-spectrum
  - manzoor-separation-does-not-specify-haar-cylinders
---

Equivariance of the stabilizer map gives `(MKG2)` pointwise.  Since its
pushforward is `mu`, pullback preserves the trace and the `L^2` norm, proving
`(MKG3)` and the universal zero-chaos obstruction.

In the AGV model, condition on `H`.  The label space is the product
`[0,1]^(Gamma/H)`.  Expanding its infinite tensor product in the basis
`1,e_1,e_2,...` gives one orthonormal vector for every finitely supported
positive-integer coloring of `Gamma/H`.  Integrating these fibers over
`(Sub(Gamma),mu)` proves `(MKG4)`; the empty coloring consists exactly of
functions of `H` alone.  Indicator functions of cylinders then give `(MKG5)`.

`manzoor-separation-does-not-specify-haar-cylinders` proves that the paper's
one-word data `(MKG6)` do not recover these joint cylinders, and its source
audit records the unnamed game, IRS strategy and extreme-point choices.  The
proof of Manzoor's main theorems invokes AGV only after those choices.  CDI
Theorem D subsequently asserts an existential relation embedding and names
no actor action, so it supplies no replacement Koopman representation.
These observations prove the claim.
