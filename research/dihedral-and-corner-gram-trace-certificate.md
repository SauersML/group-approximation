---
rg: 2
id: dihedral-and-corner-gram-trace-certificate
kind: route
title: Average a finite generalized dihedral subgroup and apply two corner Gram estimates
target: leavitt-single-cycle-trace-controls-finite-sets
requires:
  - binary-leavitt-elementary-group-is-simple
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-units-generated-by-c3-and-c2-cubed
artifacts:
  - research/artifacts/leavitt-single-c-trace-certificate-2026-09-08.md
---

Embed `(C_3)^r semidirect C_2` in a finite coefficient matrix block
with one unused coordinate. All nonidentity elements of the normal
subgroup are conjugate in `H` to the native cycle, and the inverter
is conjugate to a constant root. Approximate averaging and spectral
rounding yield `|tr U|<=3^(-r)+|tr C|+17 epsilon` for that root.

Explicit corner conjugators give arbitrary finite families whose
pairwise quotients are conjugate to the root. Prefix localization
and simplicity give a second such family for any nonidentity unit,
with pairwise quotients in a proper corner. Applying Cauchy--Schwarz
twice gives the stated finite trace bound. Literal nested quotient
words prevent extra multiplication errors. The artifact proves
termination of native-word and conjugator selection as well as all
numerical constants.
