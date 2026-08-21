---
rg: 2
id: atlas-t30-ceiling-from-parabolic-c3-energy
kind: route
title: Telescope the shortest P-C3-P word to the q14 transverse threshold
target: atlas-a4-t30-energy-ceiling-below-q14-wall
requires:
  - atlas-t30-is-one-parabolic-c3-bridge
  - atlas-a4-parabolic-c3-bridge-energy-ceiling
---

Apply `(T30-PC3-3)` pointwise to the normalized packet sequence:

```text
x30(U_n)^2<=3E_PC3(U_n).
```

The strict ceiling `(A4-PC3-CEIL)` therefore gives

```text
limsup_n x30(U_n)^2<3/6=1/2,
```

which is exactly `(T30-CEIL)`.

