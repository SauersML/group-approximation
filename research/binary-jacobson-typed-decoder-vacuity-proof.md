---
rg: 2
id: binary-jacobson-typed-decoder-vacuity-proof
kind: route
title: Use the no-head gap below threshold and a fixed spectral default above it
target: binary-jacobson-typed-square-decoder-is-still-target-equivalent
requires:
  - finitely-presented-marked-involution-corona-gap
  - positive-toeplitz-head-is-square-defect-or-rectangular-escape
---

Assume first that the stated decoder exists and suppose a corona
homomorphism retains `w_T`.  On a subsequence its rounded negative cut is
nonzero, while the finite-presentation defect `epsilon_n` tends to zero.
The decoder gives nonzero `P_n<=C_n` and contractions in the square corner
with

```text
delta_n=||Y_nX_n-C_n||_op <= omega(epsilon_n),
eta_n=||P_n-(C_n-X_nY_n)||_op <= omega(epsilon_n).
```

For all sufficiently large `n`, the sparse square-matrix inequality gives

```text
1=||P_n||_op <= eta_n+delta_n/(1-delta_n),
```

whose right side tends to zero.  This contradiction proves `(JTE1)`.

Conversely, assume `(JTE1)`.  The marked-involution corona-gap theorem gives
`gamma>0` such that a nonzero rounded negative cut implies
`Def_R(U)>=gamma`.  Take the full finite relator list together with the mark
word as the fixed named package.  Define the deterministic operation

```text
C(U)=P(U)=P_-(w_T(U)),             X(U)=Y(U)=C(U).       (JTE2)
```

These are fixed spectral and compressed matrix expressions in the named
word evaluations.  Whenever `C(U)!=0`, they are nonzero projections and
contractions in `C(U) M_d(C) C(U)`, with

```text
||Y(U)X(U)-C(U)||_op=0,
||P(U)-(C(U)-X(U)Y(U))||_op=1.                          (JTE3)
```

Set

```text
omega(epsilon)=min(1,epsilon/gamma).
```

This modulus tends to zero.  If `epsilon<gamma`, no tuple satisfying the
decoder antecedent exists.  If `epsilon>=gamma`, then `omega(epsilon)=1`,
so `(JTE3)` proves `(JSD1)`.  Thus even the fixed-package, fixed-operation,
uniform-modulus assertion follows from the target itself, completing the
equivalence.

