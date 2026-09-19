---
rg: 2
id: fanizza-et-al-computable-bcs-signal-family
kind: claim
title: Every RE set has a computable BCS family with a distinguished signal and linear strategy-collapse modulus
---

For every recursively enumerable set `L subset N`, there is a computable
family of finite Boolean constraint systems `B_m`, distinguished variables
`x_D`, and positive integers `C_m` such that, writing

```text
D=(1-x_D)/2,
```

the following hold:

```text
m in L
  => the BCS algebra A(B_m) has a tracial state tau with tau(D)>0;    (FBS1)

m notin L
  => every epsilon-perfect strategy S for the BCS game satisfies
     phi_S(D)<=C_m epsilon.                                         (FBS2)
```

The map `m |-> (B_m,C_m)` is total and computable. In particular, `C_m`
depends only on the input code, not on whether or when its recognizing
machine eventually halts.

This is Definition 4.1 together with Theorem 4.4 of Fanizza--Kroell--Mehta--
Paddock--Rochette--Slofstra--Zhao, arXiv:2510.04943v4.
