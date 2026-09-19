---
rg: 2
id: deligne-triple-cover-exact-mf-radical-proof
kind: route
title: Combine central MF invisibility with the exact Deligne finite residual
target: deligne-triple-cover-exact-mf-radical
requires:
  - deligne-triple-cover-central-generator-is-mf-radical
  - deligne-triple-cover-finite-residual-is-center
---

The first prerequisite and normality of the MF radical give

```text
C_3=<z> <= Rad_MF(E_3).
```

Every finite group is MF, hence every finite quotient is an MF detector and

```text
Rad_MF(E_3) <= Res_fin(E_3).
```

The second prerequisite identifies the right-hand side with `C_3`.  The two
inclusions prove `Rad_MF(E_3)=C_3`; membership of `z` follows immediately.
