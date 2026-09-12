---
rg: 2
id: order-seven-first-exit-supplies-same-gram-mass
kind: claim
title: The order-seven first-exit cut authenticates the positive same-Gram carrier
refuted_by: order-seven-first-exit-is-not-seven-step-leakage
distinct_from:
  native-whitehead-hecke-head-has-order-seven-anchor: that proves exact spectator coercivity on a reducing packet carrier; this claims that a low first-exit Gram cut inherits enough of the seventh-power identity.
  growing-multicut-el20-order-seven-inheritance: that asks for orbit-saturated moving cuts controlling every stage of the seven-cycle; this uses only the first-exit operator of one fixed source cut.
---

**REFUTED SHORTEST-ACTOR MECHANISM.**  Let `T=Jv` be either native mixed
Whitehead--Hecke word from
`native-whitehead-hecke-head-has-order-seven-anchor`, so `T^7=1` and its odd
occurrence detects a multiplicity involution exactly.  The proposed shortcut
was to take a source projection `Q`, cut its first-exit operator

```text
L=Q T^*(1-Q)T Q,
```

and use a positive low-spectral subprojection `E<=Q` as the Gram carrier.
Small `L` on `E` was claimed to imply

```text
||(ETE)^7-E||_2=o(1),                                  (OSG1)
```

after which the odd order-seven identity would remove the spectator gauge and
authenticate the fixed positive same-Gram mass.

This inference is false at zero defect and fixed positive density.  Let `T`
be the seven-cycle permutation on `e_0,...,e_6`, let

```text
Q=[e_0,e_1],                  E=[e_0].                 (OSG2)
```

Then `T^7=1` and `(1-Q)TE=0`, so `LE=0` exactly.  But `ETE=0`, hence

```text
||(ETE)^7-E||_2=||E||_2.                               (OSG3)
```

Tensoring `(OSG2)` with `I_N` preserves every equality and gives
`tr(E)=1/7` in dimension `7N`.  Thus amplification, a positive-density Gram
cut, and exact first-exit control do not repair the missing seventh-power
compression.

The claim is proved false by
`order-seven-first-exit-is-not-seven-step-leakage`.  A surviving use of the
order-seven actor must control `(1-E)TE` or all six orbit exits
`(1-Q)T^kE`, `1<=k<=6`; first-exit localization alone cannot supply the
same-Gram certificate.
