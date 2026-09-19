---
rg: 2
id: atlas-q1920-module-structure-proof
kind: route
title: Compute the normal module and the shared-involution lift mismatch in both marked Q1920 classes
target: atlas-q1920-is-radial-holonomy-extension
requires:
  - atlas-a5-seam-obstruction-is-not-universal
artifacts:
  - experiments/atlas_a4_q1920_module_structure.g
  - research/artifacts/atlas-a4-q1920-module-structure.json
---

The verifier starts from the complete local coset-action census through
degree twelve and selects exactly the two faithful order-1920 images.  GAP's
exact normal-subgroup lattice gives `(Q1920-MOD-1)` and the four complement
classes.  Conjugacy classes contained in `V` give orbit/span pairs

```text
(1,1), (1,2), (15,32), (15,32).
```

This proves the fixed-line and irreducible-quotient assertions without
choosing coordinates.

The verifier then computes the images of `A` and `B` under the canonical
map to `Q/V`.  Exact subgroup intersection and closure give orders two and
sixty in the quotient, versus orders one and 1920 upstairs.  Comparing the
three canonically labeled involutions in each radial `S3` finds a unique
matching quotient pair, labeled `(3,3)`.  Direct closure computes order 32
for the normal closure of their lift mismatch.  All these outputs agree for
both marked classes.
