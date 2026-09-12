---
rg: 2
id: scalar-covariant-retract-multiplicative-domain-proof
kind: route
title: Use split norm equality to make every scalar coefficient unimodular
target: scalar-covariant-odd-even-ucp-retract-is-impossible
requires:
  - deligne-triple-cover-fd-central-invisibility
  - metaplectic-half-class-has-an-exact-finite-model
  - maslov-mod3-gap-is-metaplectic-base-degree-six-gap
---

For every `s in Sigma`, complete contractivity of `i` and `r`, `(SCR1)`, and
`(SCR2)` give

```text
1=||u_s^alpha||
 <=||i(u_s^alpha)||
 =|c_s|
 <=1.
```

Therefore `|c_s|=1`, and `i(u_s^alpha)` is unitary.  Equality in both
Schwarz inequalities puts `u_s^alpha` in the multiplicative domain of `i`.
The chosen unitaries generate `A_alpha`, so `i` is a unital star-homomorphism.

The even fibre has a nonzero finite-dimensional representation: the trivial
character at `epsilon=0`, and the exact metaplectic model at `epsilon=1/2`.
Compose its matrix amplification with `i`.  For `alpha=1/3,2/3` this
contradicts `deligne-triple-cover-fd-central-invisibility`; for
`alpha=1/6,5/6` it contradicts the full order-three finite residual of `E_6`
recorded in `maslov-mod3-gap-is-metaplectic-base-degree-six-gap`.  Hence
`(SCR1)--(SCR2)` cannot exist.
