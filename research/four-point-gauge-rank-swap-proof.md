---
rg: 2
id: four-point-gauge-rank-swap-proof
kind: route
title: Compute the two complementary controlled-Pauli commutators
target: four-point-gauge-orbit-has-balanced-derived-rank-swap
requires:
  - regular-gauge-orbit-contains-equal-scale-derived-d8-reset
---

All four operators in `(GRS1)` are self-adjoint unitaries.  Their two pairs
have orthogonal nontrivial supports, so every cross commutator is one.

For involutions `X,Z` with `XZ=-ZX`,

```text
[X,Z]=XZXZ=-I=J.
```

Hence the first controlled pair has commutator

```text
E_+ tensor I + E_- tensor J
 = E_+ - E_-
 = s,
```

and the complementary pair has commutator

```text
E_+ tensor J + E_- tensor I
 = -E_+ + E_-
 = -s
 = Js.
```

On an `s=+1` block the first pair is identity and the second is `(X,Z)`; on an
`s=-1` block the roles reverse.  This proves `(GRS2)` and the constant-rank
statement.  The relations show directly that the abstract packet is a finite
class-two `2`-group.

