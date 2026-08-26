---
rg: 2
id: partial-whitehead-fold-return-s6-proof
kind: route
title: Factor the authenticated fold transporter inside the six-point model
target: partial-whitehead-fold-return-has-finite-s6-model
requires:
  - intermediate-fold-arm-has-finite-s6-model
---

All relations `(PFR1)` were verified in
`intermediate-fold-arm-s6-proof`.  It remains only to check `(PFR2)`.
Conjugating `(4 6)` by `S=(3 4)(5 6)` sends its two points to `3,5`, so

```text
S(4 6)S=(3 5).
```

Equivalently, for `U=S` and `V=(3 5)`,

```text
UVU=(4 6)=W.
```

The transposition `P=(1 2)` has disjoint support from `U`, hence
`PUP^(-1)=U=S`.  Finally `Q=(3 6)` sends the pair `{3,5}` to `{6,5}`, so

```text
QVQ^(-1)=(6 5)=T.
```

This proves every new factorization and occurrence-transport row.  Since
`M=(3 4)(5 6)` is nonidentity, its left regular translation has trace zero
and normalized Hilbert--Schmidt distance `sqrt(2)` from the identity.

