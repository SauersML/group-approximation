---
rg: 2
id: single-selected-atom-escape-compiler-proof
kind: route
title: Join the escaped atom to the current hull and iterate its trace growth
target: single-selected-atom-escape-compiler
requires:
  - maximal-forbidden-atom-has-a-named-positive-half
---

The Pauli trace flip proves `(SEC3)` exactly after rounding, with the stated
fixed perturbation loss.  The projection identity in `(SEC4)`, `(SAE1)`, and
`(MFA2)` give `(SEC5)`.  For fixed marked separation `delta>0`, choose `N`
with

```text
(1+gamma)^N delta^2/8>1.
```

The finite geometric sum of the `O(sqrt(E))` losses is independent of matrix
dimension, so sufficiently small `E` is impossible.  Hyperlinearity would
give arbitrarily accurate canonical microstates keeping the nontrivial
central involution separated, yielding the contradiction.  The exact
tracial extension witnesses that `J` is nontrivial in the abstract group.

