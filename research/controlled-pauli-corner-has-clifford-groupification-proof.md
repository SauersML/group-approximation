---
rg: 2
id: controlled-pauli-corner-has-clifford-groupification-proof
kind: route
title: Identify the corner block with CZ and apply the unique Pauli spin type
target: controlled-pauli-corner-has-clifford-groupification
requires:
  - finite-schur-clifford-packet-flexible-hs-exactification
artifacts:
  - experiments/controlled_corner_clifford_groupification.py
---

In exponent coordinates `(X1,Z1,X2,Z2)`, `(CPC1)` is the linear map whose
columns are

```text
(1,0,0,1), (0,1,0,0), (0,1,1,0), (0,0,0,1).
```

Direct multiplication over `F_2` shows that it squares to the identity and
preserves the alternating form `diag(H,H)`. The displayed images are
involutions, so the quadratic refinement is preserved as well. Thus `theta`
is an involutive automorphism of `P` and `(CPC2)` is finite.

In the standard spin representation take `Z1=Z tensor I` and
`Z2=I tensor Z`. Formula `(CPC3)` is `diag(1,1,1,-1)`. Direct calculation
gives

```text
C_Z X1 C_Z=X1 Z2,     C_Z Z1 C_Z=Z1,
C_Z X2 C_Z=Z1 X2,     C_Z Z2 C_Z=Z2.
```

The `J=-1` sector of the extraspecial group `P` has one irreducible type `S`,
of dimension four. Therefore the restriction of any marked representation
of `G_CZ` to `P` is `S tensor I_M`. Both `rho(t)` and `C_Z tensor I_M`
implement `theta`; their quotient commutes with `S(P) tensor I_M`. Schur's
lemma gives `rho(t)=C_Z tensor V`. Since both `rho(t)` and `C_Z` square to
the identity, `V` is a self-adjoint involution. This proves `(CPC4)` and the
covariance claim. The robust final sentence is the fixed-finite-group case
of the required exactification theorem.
