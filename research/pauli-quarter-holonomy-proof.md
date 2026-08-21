---
rg: 2
id: pauli-quarter-holonomy-proof
kind: route
title: Evaluate the two-projection commutator on the atlas moments
target: two-pauli-quarter-carriers-have-fixed-reflection-holonomy
requires: []
---

Exact prefix arithmetic gives
`tau(F)=tau(G)=1/4`, `tau(FG)=1/16`, and `tau(FGFG)=3/64`.  For projection
reflections `R_F=2F-1`, `R_G=2G-1`, the standard two-projection expansion is

```text
||R_FR_GR_FR_G-I||_2^2
 =32[tau(FG)-tau(FGFG)]=1/2.
```

The exact reduced product has `(R_FR_G)^4=1` but
`(R_FR_G)^3!=1`; since the generators are involutions and do not commute,
they generate `D_8`.  Its central commutator is
`K=(R_FR_G)^2`, with `K^2=1` and `tau(K)=3/4`.  Hence
`H=(1-K)/2` has trace `1/8`.  Multiplying the commutator relation by `H`
gives `HR_FR_G=-HR_GR_F`, the asserted Pauli anticommutation.
