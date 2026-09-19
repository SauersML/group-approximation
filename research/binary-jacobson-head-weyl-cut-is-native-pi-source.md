---
rg: 2
id: binary-jacobson-head-weyl-cut-is-native-pi-source
kind: claim
title: The Jacobson head-Weyl overlap is a nonzero native degree-two PI source
artifacts:
  - research/binary-jacobson-head-weyl-cut-pi-source-proof.md
distinct_from:
  binary-jacobson-head-sector-has-native-two-qubit-packet: that identifies the uncompressed head sector as a degree-four target; this cuts it by a literal constant-Weyl conjugate of the head and obtains a degree-two source.
  binary-jacobson-naive-head-polar-is-balanced-return: that computes the raw rectangular return from this cut; this proves independently that its initial cut is nonzero whenever the head survives and computes the PI degree of the compressed packet.
  binary-jacobson-raw-cycle-selects-common-pi-intertwiner: that asks for a common return from a degree-two source to the literal degree-four target; this supplies the source canonically but not the unequal-degree target occurrence.
---

**ESTABLISHED.**  On the negative head cut

```text
P=(1-rho(x_13(Q)))/2
```

of any finite-dimensional unitary representation, use the native packet

```text
X_0=x_12(Q),   Z_0=x_23(1),
X_1=x_14(Q),   Z_1=x_43(1).
```

Let `Y=x_23(Q)=w_12 x_13(Q)w_12^(-1)` and let

```text
E=P(1-rho(Y))/2.                                         (JWS1)
```

Then `E` is nonzero whenever `P` is nonzero.  Indeed `Y` commutes with the
head, while

```text
X_0 Y X_0^(-1)=x_13(Q)Y,                                (JWS2)
```

so on `P` the unitary `X_0` exchanges the two sign cuts of `Y`.  They have
equal rank and sum to `P`.

The projection `E` commutes with `Z_0,X_1,Z_1`, whereas `(JWS2)` gives

```text
E X_0 E=0.                                               (JWS3)
```

On `E`, the last pair remains Pauli,

```text
(E X_1 E)(E Z_1 E)=-(E Z_1 E)(E X_1 E),                 (JWS4)
```

and `E Z_0 E` is a commuting involution.  Consequently the compressed
four-tuple

```text
C=(E X_0 E,E Z_0 E,E X_1 E,E Z_1 E)
```

generates a quotient of `M_2(C) directSum M_2(C)` and obeys

```text
s_4(C_1,C_2,C_3,C_4)=0.                                 (JWS5)
```

This gives a canonical, occurrence-typed, nonzero degree-two source for the
sparse PI endpoint.  It does **not** finish the bridge: conjugating this
corner by the balanced occurrence transports it to an isomorphic degree-two
corner.  What remains is to authenticate, with the same return occurrence,
the literal uncompressed native degree-four tuple on the target side.

DERIVATION
binary-jacobson-head-weyl-cut-pi-source-proof
