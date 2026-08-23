---
rg: 2
id: positive-mass-four-pauli-intertwiner-forces-pi-gap
kind: claim
title: A positive-mass common four-Pauli intertwiner already forces the PI gap
distinct_from:
  one-common-intertwiner-carries-the-four-pauli-pi-bridge: that asks for an almost-unitary intertwiner on an entire positive corner; this proves that a contraction of any fixed positive HS mass suffices.
  four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap: that compares two complete tuples on one corner; this permits a noninvertible common intertwiner and tests the target only on its mass.
---

**ESTABLISHED.**  Let `D_1,...,D_4` be unitaries, let
`C_1,...,C_4` be contractions in one algebra `M_2 tensor I`, and let `T` be
a contraction.  Put

```text
epsilon_PI=||s4(D)-8D_1D_2D_3D_4||_2,
epsilon_j=||D_jT-TC_j||_2.
```

Then

```text
8||T||_2 <= epsilon_PI+24 sum_(j=1)^4 epsilon_j.       (PMI1)
```

In particular, if `||T||_2^2>=beta>0`, the two-qubit Pauli residuals tend
to zero, and all four intertwining residuals tend to zero, one obtains the
fixed contradiction `8sqrt(beta)<=o(1)`.  Neither invertibility nor
near-unitarity of `T` is needed.  The conclusion is invariant under tensoring
all data with an arbitrary spectator identity.
