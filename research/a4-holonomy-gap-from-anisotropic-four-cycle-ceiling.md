---
rg: 2
id: a4-holonomy-gap-from-anisotropic-four-cycle-ceiling
kind: route
title: The weighted four-cycle ceiling is already the exact raw-S3 contradiction budget
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-anisotropic-four-cycle-ceiling
  - atlas-a8-four-cycle-controls-raw-s3-energy
---

Write

```text
D_ij(n)=1-Re tau_n(V_n(tij)).
```

The proof of `atlas-a8-four-cycle-controls-raw-s3-energy` keeps the two raw
coordinates separate before its final symmetric relaxation.  For the first raw
involution `h_a=t21`, the exact eight-letter identity

```text
t21=t01 t30 t23 t30 t01 t30 t23 t30
```

gives

```text
a_n^2 <= 24(d_01^2+d_23^2+d_30^2)
      = 48(D_01+D_23+D_30),
```

where `d_ij^2=2D_ij`.  The second raw involution is already the cycle generator
`h_b=t12`, hence exactly

```text
b_n^2=d_12^2=2D_12.
```

Therefore

```text
a_n^2+b_n^2
 <= 2(24(D_01+D_23+D_30)+D_12).
```

The strict ceiling in `atlas-a4-anisotropic-four-cycle-ceiling` now yields

```text
limsup_n (a_n^2+b_n^2) < 2/256 = 1/128,
```

which is precisely `atlas-a4-holonomy-coherence-gap`.

This route removes the artificial requirement that the directly observed
`t12` direction pay the same worst-case eight-letter synthesis coefficient as
the three directions used only to manufacture `t21`.