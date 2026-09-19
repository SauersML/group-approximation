---
rg: 2
id: qutrit-diamond-robustly-synchronizes-pvms
kind: claim
title: A five-edge 3-colouring diamond robustly synchronizes two qutrit PVMs
artifacts:
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
distinct_from:
  qutrit-fixed-space-projector-synchronizer: that now-refuted endpoint asked for ordinary group-word defects and complement-flexible exact extension; this valid claim supplies only the desired tracial inequality using projection-overlap defects.
  rank-conjugacy-detects-projection-overlap: that charges one supplied overlap by a two-copy conjugacy defect; this combines five overlap atoms into qutrit PVM synchronization but does not authenticate the hybrid blocks.
  k3-relational-atlas-to-scalar-group-words: that asks for a full scalar-word compiler for a 3-colouring atlas; this is one constant-size operator inequality inside that atlas.
---

Let `{P_c(z)}_(c in Z_3)` be a PVM for each of `z=x,y,a,b`.  For a triangle
define its same-colour overlap defect by

```text
D(x,a,b)=sum_c (
 ||P_c(x)P_c(a)||_2^2
+||P_c(x)P_c(b)||_2^2
+||P_c(a)P_c(b)||_2^2 ).                               (QDS1)
```

For the two triangles `(x,a,b)` and `(y,a,b)` sharing the edge `(a,b)`,

```text
sum_c ||P_c(x)-P_c(y)||_2^2
 <=4(D(x,a,b)+D(y,a,b)).                                (QDS2)
```

Thus the five-edge diamond is an outcome-count-independent, linear-defect
synchronizer for the complete qutrit measurement.  The remaining group
problem is only to charge its same-colour overlap defects by ordinary word
defects without imposing literal cyclic-subgroup equality.
