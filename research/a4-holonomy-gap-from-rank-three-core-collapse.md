---
rg: 2
id: a4-holonomy-gap-from-rank-three-core-collapse
kind: route
title: Rank-three commutant collapse kills the two raw S3 covariance directions
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-rank-three-core-commutant-collapse
  - atlas-a4-rank-three-core
---

Let `U_n` be the relative chart frame and

```text
H=diag(GL_3(F2),1).
```

By the rank-three core collapse, choose `Y_n in lambda_(k_n)(H)'` with

```text
||U_n-Y_n||_2 -> 0.
```

The two involutions `h_a,h_b` defining the covariance coordinates in the
target belong to this standard rank-three `H` by the raw-S3 localization.
Therefore, for `h` equal to either one,

```text
||U_n lambda(h)-lambda(h)U_n||_2
 <= ||(U_n-Y_n)lambda(h)||_2
    +||lambda(h)(U_n-Y_n)||_2
 <= 2 ||U_n-Y_n||_2 -> 0.
```

Hence

```text
a_n^2+b_n^2 -> 0,
```

so in particular

```text
limsup_n (a_n^2+b_n^2)=0 < 1/128.
```

This proves the A4 holonomy coherence gap while using only the fourteen-word
rank-three packet core and collision `19243`; the sixteen central-C3 pair-cubes
and full-A8 commutant synchronization are bypassed.
