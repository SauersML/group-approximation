---
rg: 2
id: nonhyperlinear-via-simultaneous-character-packing
kind: route
title: Pack every forbidden root atom into one marked-sector orthogonal family
target: non-hyperlinear-group
requires:
  - mipstar-bcs-tracial-nonru-exists
  - finite-pauli-seed-reducing-quarter-carrier
  - simultaneous-character-packing-removes-max-loss
  - simultaneous-bad-character-packing-extension
---

**INVALIDATED.**  Its packing prerequisite is refuted by
`canonical-trace-forbids-supercritical-character-packing`: the canonical
trace gives `K<=2/beta`, while the route requires a strictly larger `K`.

Use the exact tracial representation from
`simultaneous-bad-character-packing-extension` to see that the central mark
`J` is nontrivial.  In hypothetical canonical matrix microstates,
`finite-pauli-seed-reducing-quarter-carrier` gives

```text
tr(Q_empty)->1/4,              tr(Q_-)->1/2.            (NSP1)
```

Robust contextual soundness supplies

```text
sum_i tr(e_i)>=beta tr(Q_empty)-o(1).                   (NSP2)
```

The joint relations `(SBP3)` and fixed-word exactification give `K` mutually
orthogonal conjugates of every `e_i`, all orthogonal across different `i` as
well.  Hence

```text
K sum_i tr(e_i)<=tr(Q_-)+o(1).                          (NSP3)
```

Taking limits gives `K beta/4<=1/2`, contrary to
`K=floor(2/beta)+1`.  Therefore the presented group has no canonical matrix
microstates and is nonhyperlinear.
