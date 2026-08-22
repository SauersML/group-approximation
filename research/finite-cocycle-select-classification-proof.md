---
rg: 2
id: finite-cocycle-select-classification-proof
kind: route
title: Solve the shift edge equations and compress to the uniform vector
target: finite-cocycle-select-forces-one-common-lcu-gauge
requires:
  - right-regular-covariance-forces-one-common-router
  - grading-zero-corner-does-not-orient-controlled-payload
---

Let `p_x` be the one-negative lamp atoms.  Their sum `e_nat` is invariant
under the shifts and hence central in the finite wreath group; orthogonality
of the atoms gives canonical trace `|K|/2^|K|`.  The regular action on their
labels is free, so the corresponding induced packet is irreducible.
Commutation of `C` with every lamp makes `e_nat` reducing and gives

```text
C=directSum_(x in K) C_x.
```

The second relation in `(FCS1)`, evaluated on the `x` coordinate, is

```text
C_x C_(g^(-1)x)^(-1)=w_g.                               (FCP1)
```

Taking `g=x` and `x` as the coordinate (or following a fixed generator word
from the identity) gives `C_x=w_x A`, where `A=C_e`.  Conversely the
homomorphism law gives

```text
w_x A (w_(g^(-1)x)A)^(-1)=w_g,
```

so every `A` yields a solution.  This proves `(FCS2)`.  Compression to the
uniform vector averages the diagonal blocks and gives `(FCS3)`; right
multiplication by a unitary preserves normalized HS norm.

Conjugating `L_gL_h=L_(gh)` by `C` and using that control shifts commute with
payload words yields

```text
w_(gh)L_(gh)=w_gw_hL_(gh),
```

which proves `(FCS4)`.  The cocycle variant follows by moving `w_h` through
`L_g` using the prescribed payload action.  Fixed finite conditional
expectations onto the lamp diagonal and finite telescoping over `K` give the
stated dimension-independent robust form after packet exactification.
