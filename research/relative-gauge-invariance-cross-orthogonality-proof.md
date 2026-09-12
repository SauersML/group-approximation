---
rg: 2
id: relative-gauge-invariance-cross-orthogonality-proof
kind: route
title: Expand the relative branch gauge and apply the tracial L2 triangle inequality
target: relative-gauge-invariance-transfers-cross-orthogonality
requires:
  - two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge
---

Put `V=U_0^*U_1`.  Unitary invariance gives

```text
||Q_0Q_1||_2=||P_0VP_1||_2=||P_0VP_1V^*||_2.
```

Expanding

```text
P_0P_1=P_0VP_1V^*+P_0(P_1-VP_1V^*)
```

and using that left multiplication by a projection is an `L^2` contraction
proves the first estimate.  Conjugating `Q_0Q_1` by `U_1` instead gives

```text
||Q_0Q_1||_2=||V^*P_0VP_1||_2,
```

and the identical expansion with `P_0` proves the second.  Taking the better
of the two estimates is `(RGI2)`.

For `(RGI5)`, apply the required Pauli gauge-lock theorem to obtain `W` in
the common Pauli commutant.  Because `P_1` belongs to the Pauli algebra,
`WP_1W^*=P_1`; expanding `VP_1V^*-WP_1W^*` gives `(RGI4)`, and substitution
in the first half of `(RGI2)` finishes the proof.
