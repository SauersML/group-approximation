---
rg: 2
id: atlas-common-u-second-moment-is-one-projection-gram
kind: claim
title: Each common-U transvection second moment is one quadratic projection-Gram coordinate
distinct_from:
  canonical-trace-tests-robustify-pauli-quarter-holonomy: that expands the commutator norm of two fixed packet reflections; this applies to every common relative unitary U and identifies the exact scalar which distinguishes hub and leaf covariance spectra.
  atlas-a4-classical-opaque-star-sharp-constant: that computes full optimal spectral matching on sixty finite sectors; this is a dimension-free identity for arbitrary matrix multiplicity.
---

Let `t` be any involution in an exact unitary representation, put

```text
P_t=(1+t)/2,       Q_t=U P_t U^*,
V_t=U t U^* t=(2Q_t-1)(2P_t-1).
```

Then

```text
tau(V_t^2)
 =1-16 [tau(P_t Q_t)-tau(P_t Q_t P_t Q_t)].           (A4-GRAM-2)
```

The right side is real.  Thus the second spectral moment of every opcode in
the A4 opaque star is exactly one quadratic projection-Gram scalar of the same
common relative unitary `U`.

For two opcodes `V_s,V_t`, unitary word Lipschitzness gives

```text
|tau(V_s^2)-tau(V_t^2)|
 <=2 inf_(A unitary)||V_s-A V_t A^*||_2.              (A4-MOM-ORBIT)
```

Consequently second-moment transport is a necessary scalar shadow of the
opaque-star compiler.  On the sixty classical packet sectors its sharp ratio
to `||q_19243-1||_2` is `1/sqrt(2)`: an order-two opcode has second regular
moment one, while order-three and order-four opcodes have second regular
moment zero.  This identity survives arbitrary external amplification, but it
does not by itself relate different `t`; that relation remains the
collision-assisted common-`U` gate.
