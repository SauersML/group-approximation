---
rg: 2
id: projection-crt-common-meet-proof
kind: route
title: Take complements inside the CRT projection and apply the projection union bound
target: projection-crt-deficit-forces-common-meet
requires:
  - shared-involution-right-ideal-interpolation-criterion
---

Because `p q_i=r_i` is self-adjoint, taking adjoints gives `q_i p=r_i`.
Thus `p` and `q_i` commute, `r_i<=p`, and

```text
p-r_i=p(1-q_i)
```

is a projection of trace at most `tau(1-q_i)=delta_i`.  Inside the finite
projection lattice below `p`, De Morgan's law and subadditivity of dimension
give

```text
p-meet_i r_i=join_i(p-r_i),
tau(p-meet_i r_i)<=sum_i tau(p-r_i)<=sum_i delta_i.
```

This proves `(PCM3)--(PCM5)`.  For two projections, `r_1 join r_2<=p` and
modularity of the finite trace give

```text
tau(r_1)+tau(r_2)-tau(r_1 meet r_2)
 =tau(r_1 join r_2)
 <=tau(p)<=tau(r_1)+delta_1.
```

Cancel `tau(r_1)` to obtain the first inequality in `(PCM6)`; interchange
the indices for the second.  The matrices in `(PCM7)` are direct
calculations.  Distinct nonorthogonal rank-one projections do not commute,
their join has rank two, and every displayed trace loss is one rank.
