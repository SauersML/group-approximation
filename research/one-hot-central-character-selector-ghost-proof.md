---
rg: 2
id: one-hot-central-character-selector-ghost-proof
kind: route
title: Multiply selector-trivial character ratios to create the weight-three block
target: one-hot-central-character-selector-forces-weight-three-ghost
requires: []
---

The product in `(CCG3)` is a one-dimensional representation because the
one-dimensional representations of `G` form a group under pointwise
multiplication.  On `Z` its value is

```text
zeta^3 zeta^(-1) zeta^(-1)=zeta.
```

For each involution `r_b`, every value is `+1` or `-1`, so inverses have the
same value.  The negative coordinate set of a product is the symmetric
difference of the negative coordinate sets of its factors.  Applying that
observation to `(CCG3)` gives `{0,1,2}` exactly.

If a selected semisimple group-algebra corner realizes arbitrary
four-outcome PVMs, it realizes each deterministic PVM.  Those four corner
characters extend to one-dimensional group representations carrying the
same central selector and satisfying `(CCG1)`.  The constructed `psi` is
therefore another one-dimensional block in the same selected corner, but
its joint signs violate the exactly-one condition.  This proves the claimed
selector obstruction.
