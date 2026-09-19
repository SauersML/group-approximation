---
rg: 2
id: atlas-19243-relation-forces-s3-distance-proof
kind: route
title: Compare the kernel relation directly with its fixed S3-commutant value
target: atlas-19243-relation-forces-s3-distance
requires:
  - atlas-19243-s3-relative-normal-form
  - atlas-word-19243-is-kernel-relation
artifacts:
  - experiments/atlas_19243_s3_gap.py
---

For every `V in C_K`, `atlas-19243-s3-relative-normal-form` and its exact
replay give

```text
q(V)=rho(b),
```

where `b` is a nonidentity involution of `A8`.  The amplified regular
character therefore gives

```text
||q(V)-1||_2=||rho(b)-1||_2=sqrt(2).                 (1)
```

Only the four second-chart syllables of `q` depend on the relative frame.
For a fixed unitary `A`, bi-invariance gives

```text
||UAU^*-VAV^*||_2
 <= ||(U-V)AU^*||_2+||VA(U^*-V^*)||_2
 <= 2||U-V||_2.                                      (2)
```

Telescoping the four variable syllables and using `(2)` yields

```text
||q(U)-q(V)||_2 <= 8||U-V||_2.                       (3)
```

By the reverse triangle inequality and `(1)--(3)`,

```text
sqrt(2)
 <= ||q(V)-q(U)||_2+||q(U)-1||_2
 <= 8||U-V||_2+||q(U)-1||_2.
```

Rearrange, take the positive part, and infimize over `V in C_K`.  This proves
`(19243-REL-DIST)`.  Sending the relation defect to zero gives
`(19243-REL-WALL)`.

The constant differs from the centrality theorem for a precise reason.  The
centrality word contains `q` and `q^*`, and therefore incurs a second factor
two.  A necessity sequence pulled back from `Q` kills `q` itself and does not
pay that factor.
