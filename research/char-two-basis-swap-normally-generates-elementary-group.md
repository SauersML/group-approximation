---
rg: 2
id: char-two-basis-swap-normally-generates-elementary-group
kind: claim
title: A basis transposition normally generates every rank-at-least-three elementary group in characteristic two
distinct_from:
  leavitt-gl-equals-el-and-perfect-unit-group: that identifies GL with EL for one self-similar ring; this is a general characteristic-two normal-generation calculation valid over every unital F2-algebra.
  leavitt-cylinder-swaps-generate-thompson-in-el: that places Thompson cylinder swaps inside a Leavitt elementary group; this computes the normal closure of the corresponding basis swap inside the whole elementary group.
---

Let `R` be a unital ring of characteristic two and `n>=3`.  In `E_n(R)` let
`tau_12` be the permutation matrix interchanging the first two basis vectors.
Then

```text
<<tau_12>>_(E_n(R)) = E_n(R).                            (CTN1)
```

The calculation is uniform in the coefficient `r in R`.  A commutator with
`e_13(r)` puts

```text
e_13(r)e_23(r)
```

in the normal closure, and conjugation by `e_12(1)` cancels the two
`e_13(r)` factors and leaves `e_23(r)`.  Index permutations then give every
elementary root `e_ij(r)`, which generate `E_n(R)`.

Characteristic two is load-bearing twice: `tau_12` itself is the elementary
word `e_12(1)e_21(1)e_12(1)` with no diagonal sign, and
`e_13(r)^2=1`, which is the cancellation in the second step.
