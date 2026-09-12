---
rg: 2
id: binary-jacobson-head-weyl-cut-pi-source-proof
kind: route
title: Cut one Pauli qubit by a Weyl-conjugate head sign
target: binary-jacobson-head-weyl-cut-is-native-pi-source
requires:
  - binary-jacobson-head-sector-has-native-two-qubit-packet
  - binary-jacobson-naive-head-polar-is-balanced-return
---

The roots `x_13(Q)` and `Y=x_23(Q)` commute, hence their spectral cuts do.
The Steinberg commutator relation gives

```text
[x_12(Q),x_23(Q)]=x_13(Q^2)=x_13(Q),                    (1)
```

because `Q^2=Q`.  The center in `(1)` commutes with both factors and every
root has order two.  Therefore

```text
X_0 Y X_0^(-1)=x_13(Q)Y.                                (2)
```

After restriction to `P`, equation `(2)` says that `X_0` conjugates `Y` to
`-Y`.  The native packet theorem says `X_0` preserves `P`.  Thus it exchanges
the positive and negative `Y` cuts inside `P`.  Their ranks agree; since
they sum to a nonzero `P`, both are nonzero.  This proves the first assertion
and `(JWS3)`.

The root `Y=x_23(Q)` commutes with `Z_0=x_23(1)` and with the two roots
`X_1=x_14(Q),Z_1=x_43(1)` (the relevant matrix units have zero products in
both orders).  Hence these three unitaries reduce `E`.  Their relations on
`E` are inherited from the native packet: `Z_0` commutes with `X_1,Z_1`,
while `[X_1,Z_1]=x_13(Q)` acts as `-1`.  Therefore `X_1,Z_1` generate an
`M_2` factor and adjoining the commuting involution `Z_0` gives a quotient
of

```text
C^*(C_2) tensor M_2(C) = M_2(C) directSum M_2(C).        (3)
```

The zero first entry in `(JWS3)` and Amitsur--Levitzki on each summand of
`(3)` prove `(JWS5)`.  Finally any unitary occurrence transporting `E`
transports its compressed algebra isomorphically, so the balanced polar by
itself cannot change this PI degree; a distinct authentication of the native
target tuple is still required.
