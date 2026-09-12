---
rg: 2
id: nonhyperlinear-via-one-btb-fiber-floor
kind: route
title: Use the protected root carrier once and charge its positive conditioned fiber directly
target: non-hyperlinear-group
requires:
  - mipstar-bcs-tracial-nonru-exists
  - maximal-forbidden-atom-has-a-named-positive-half
  - canonical-bcs-root-detection-via-binary-tetrahedral-bridge
  - protected-adaptive-btb-wordization-preserves-canonical-budget
  - payload-conditioned-btb-active-fiber-floor
---

Assume the compiled group is hyperlinear and take canonical microstates.
The protected wordization makes `tau(Q_0)->1/8`.  Apply the robust BCS gap
on this reducing carrier and choose a maximal forbidden type:

```text
tau(A_i)>=(beta/M)tau(Q_0)-o(1).                       (BAF4)
```

Equations `(BAF2)--(BAF4)` give

```text
tau(F_i)>=beta/(144M)-o(1).                            (BAF5)
```

Then `(BAF3)` gives a positive dimension-independent lower bound on the
sum of defining relator energies, contradicting the canonical microstate
defect tending to zero.  The protected perfect model keeps `J` nontrivial
and has `F_i=0`, so the abstract group is nontrivial and exactly complete.

This endpoint consumes only the first half of the former adaptive-tree
architecture.  In particular, solving `(BAF3)` would prove existence of a
non-hyperlinear group without proving `(CBR3)`.
