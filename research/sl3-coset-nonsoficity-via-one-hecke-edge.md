---
rg: 2
id: sl3-coset-nonsoficity-via-one-hecke-edge
kind: route
title: Rule out the arithmetic coset atlas using one Hecke edge and Kazhdan averaging
target: sl3-hnn-central-dual-gap-vanishes
requires:
  - sl3-prime-coset-action-exact-atlas-firewall
---

**INVALIDATED PROPOSAL.**  Exactify or Kazhdan-average the restriction of a
hypothetical arithmetic atlas to `Lambda=SL_3(Z)`, retain the single
transporter associated with

```text
h=diag(p,1,p^(-1)),
```

and try to contradict the coexistence of a `Lambda`-invariant base label
and its disjoint `h`-translate using only the conjugacy relations over
`Lambda cap h^(-1)Lambda h`.

`single-hecke-edge-has-exact-two-sheet-atlases` gives exact finite
countermodels to exactly these inputs.  The lattice action, the overlap
conjugacy, and the separated two-site labels all hold with zero error.
Therefore neither a better Kazhdan constant nor a sharper one-transporter
estimate can close this route.

The full endpoint remains open.  A replacement must use a relation joining
more than one parahoric edge--the rank-two chamber holonomy/full arithmetic
actor compatibility which prevents the sheet flip from extending to
`Gamma`.
