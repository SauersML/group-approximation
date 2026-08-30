---
rg: 2
id: coherent-heisenberg-decoder-logical-boundary-proof
kind: route
title: Apply the cyclic Leavitt trace ledger and simplicity
target: coherent-heisenberg-decoder-is-marked-nonhyperlinearity
requires:
  - binary-leavitt-elementary-group-is-simple
---

Let `tau_P` be normalized trace on the decoded corner and put

```text
a_i=Re tau_P(T_iS_i)=Re tau_P(S_iT_i).
```

The scalar identity

```text
1=(1-a_0)+(1-a_1)+(a_0+a_1-1)
```

and the triangle inequality reduce `(CHD3)` to three applications of
Cauchy--Schwarz:

```text
|1-a_i| <= ||T_iS_i-P||_(2,P),
|a_0+a_1-1| <= ||S_0T_0+S_1T_1-P||_(2,P).
```

If the errors are measured in the ambient normalized Hilbert--Schmidt norm
and `tau(P)>=alpha>0`, division by the corner scale gives the equivalent
quantitative form

```text
sqrt(alpha) <= ||T_0S_0-P||_2
              +||T_1S_1-P||_2
              +||S_0T_0+S_1T_1-P||_2.                (CHD4)
```

Hence no positive-density corner can have all three defects tending to zero.
The universal decoder assertion is therefore true exactly when its
root-surviving premise never occurs.  Finally a surviving sequence defines a
nontrivial ultraproduct homomorphism, and
`binary-leavitt-elementary-group-is-simple` makes its normal kernel trivial.
