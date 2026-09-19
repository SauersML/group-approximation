---
rg: 2
id: orthogonal-hecke-row-proof
kind: route
title: Put the defects in orthogonal matrix-unit rows
target: orthogonal-hecke-row-packs-common-source-energy-into-one-root
requires: []
---

Choose matrix units in a fixed `M_m` packet and set
`R=sum_j E_(j1) tensor D_j`.  Matrix-unit multiplication gives exactly

```text
R^*R=E_(11) tensor sum_j D_j^*D_j.
```

Taking normalized trace proves
`m||R||_2^2=sum_j||D_j||_2^2`.  Since the row has finitely many fixed Hecke
coefficients, a finitely presented coefficient ring may name it and the
Steinberg symbol `x_12(R)` is one ordinary word after the finite
ring-to-root translation.  If every `D_j` vanishes in the exact witness then
`R=0`, so this packaging preserves exact completeness.  No inference from
the root defect back to `||R||_2` is made here.
