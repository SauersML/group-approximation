---
rg: 2
id: one-hot-central-character-selector-ghost-proof
kind: route
title: Tensor deterministic sectors in a central-character-preserving three-minus-two power
target: one-hot-central-character-selector-forces-weight-three-ghost
requires: []
---

The diagonal tensor product in `(CCG3)` is a representation of `G`.  On `Z`
its value is

```text
zeta^3 conjugate(zeta)^2=zeta,
```

because `zeta` is unitary.  For each involution `r_b`, every deterministic
sector value is the scalar `+I` or `-I`, and conjugation leaves that sign
unchanged.  The negative coordinate set of a tensor product is the
symmetric difference of the negative coordinate sets of its factors.
Applying this observation to three copies of `{0}`, one copy of `{1}`, and
one copy of `{2}` gives `{0,1,2}` exactly.

If a selected semisimple group-algebra corner realizes arbitrary
four-outcome PVMs, it realizes each deterministic PVM.  Those four corner
sectors give finite-dimensional group representations carrying the same
central character and satisfying `(CCG1)`; their auxiliary generators need
not act scalarly.  The constructed `Psi` is therefore another nonzero block
in the same central-character sector, but its joint selector signs violate
the exactly-one condition.  This proves the claimed selector obstruction
without assuming that deterministic sectors are one-dimensional characters
of the whole gadget.
