---
rg: 2
id: atlas-collision-involution-is-an-a4-bridge-to-h6-proof
kind: route
title: Close the collision involution with each C3 line in the exact GL4(F2) chart
target: atlas-collision-involution-is-an-a4-bridge-to-h6
requires:
  - atlas-a4-19243-s3xs3-localization
  - atlas-a4-rank-three-core
  - a4-regular-line-sector-spectral-split
artifacts:
  - experiments/atlas_a4_19243_component_localization.py
---

The localization script uses exact `4 by 4` matrix arithmetic over `F2`.
The previously established large-component calculation gives `[b_0,K]=1`.
For the other component it selects the three elements of `H_6` having order
one or three; these form `C_6`.  Exact multiplication checks that conjugation
by `b_0` does not preserve this set.

Closing `C_6 union {b_0}` under multiplication gives twelve elements, with
one identity, three involutions, and eight elements of order three.  Hence it
is `A4`.  Direct intersection checks give

```text
<C_6,b_0> intersect H_6 = C_6,
<C_6,b_0> intersect K = 1.
```

This proves the fixed-chart assertions.  Conjugation by an arbitrary common
relative unitary `U` preserves the regular representation type and all
polynomial identities of this `A4`.  Therefore the line-sector spectral split
applies exactly to `(U^*P_6U,U^*rho(b_0)U)`, including the `2/3` gap and its
amplification independence.  No assertion about compression by the fixed
`P_6` is made; obtaining that replacement is precisely the remaining packet
transport problem.

