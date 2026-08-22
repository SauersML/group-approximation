---
rg: 2
id: full-weyl-energy-support-floor
kind: claim
title: Full Weyl energy has an exact character-support floor
---

Let `H=F_2^r`, let `X:H->U(d)` be an exact unitary representation, and let
`Z(b) in U(d)` be arbitrary unitaries indexed by `b in H` (no additive law
for `Z` is needed).  Then

```text
E_(a,b) ||X(a)Z(b)-(-1)^(a.b) Z(b)X(a)||_2^2
  >= 4(1-d/2^r).                                         (FWE1)
```

Thus every `d<=r` exact additive `X`-representation has full Weyl energy
bounded below by a universal constant for all sufficiently large `r`, no
matter how the second family is positioned.  This supplies the full-product
gap used by `private-random-weyl-sampler-forces-growing-matrix-dimension`
without an exactification or stability theorem.

DERIVATION
full-weyl-energy-support-floor via full-weyl-energy-support-floor-proof

