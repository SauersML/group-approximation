---
rg: 2
id: center-chain-four-hecke-flags-have-native-ranks
kind: claim
title: Four center-chain Hecke compressions realize the two native source and target ranks
artifacts:
  - research/center-chain-four-hecke-flag-proof.md
distinct_from:
  center-chain-hecke-polar-supports-are-nested-pauli-flags: that computes the two A-side target flags and their cross-Gram; this adds the two individual B-side source flags and records why the cumulative B-product has the wrong second source rank.
  fixed-center-chain-hecke-occurrence-is-regularly-impossible: that forbids promoting fixed positive group-algebra flags to a complete exact native occurrence row; this is only an exact rank and polar-support calculation and makes no occurrence-typing claim.
---

**ESTABLISHED FOUR-FLAG CALCULATION.**  In the literal center chain put

```text
H=<x_65(q),x_54(q),x_42(q)>,             e=e_chi,
A_1=x_47(a_1), A_2=x_58(a_2),
B_2=x_84(b_2), B_3=x_95(b_3).                         (FHF1)
```

The two individual B-side compressions and the two cumulative A-side
compressions have polar supports

```text
supp|eB_2e|       =r_1=e z_<x_82(b_2)>,
supp|eB_3e|       =r_2=e z_<x_94(b_3),x_92(b_3)>,
supp|eA_1e|       =p_1=e z_<x_57(a_1),x_67(a_1)>,
supp|eA_2A_1e|    =p_2=e z_<x_57(a_1),x_67(a_1),x_68(a_2)>.
                                                               (FHF2)
```

Relative to `e`, their traces are exactly

```text
tau(r_1)/tau(e)=1/2,    tau(r_2)/tau(e)=1/4,
tau(p_1)/tau(e)=1/4,    tau(p_2)/tau(e)=1/8.           (FHF3)
```

Thus `(r_1,p_1)` and `(r_2,p_2)` have exactly the source/target ranks
`(1/2,1/4)` and `(1/4,1/8)` of the two native selector scales.  Every
compressed operator in `(FHF2)` is a partial isometry with the displayed
support projection.  This rank match is exact but deliberately untyped: by
the regular-trace firewall it cannot alone be interpreted as a fixed exact
native occurrence row.

The individual choice of `B_3` is essential.  The cumulative product
`B_3B_2` moves the three independent center coordinates detected by
`x_82(b_2),x_94(b_3),x_92(b_3)`, so its support has relative trace `1/8`, not
the required second source trace `1/4`.

DERIVATION
center-chain-four-hecke-flag-proof

