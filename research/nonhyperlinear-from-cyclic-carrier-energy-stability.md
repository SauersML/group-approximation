---
rg: 2
id: nonhyperlinear-from-cyclic-carrier-energy-stability
kind: route
title: Contradict a strict cyclic-energy ceiling with canonical moments
target: non-hyperlinear-group
requires:
  - cyclic-carrier-energy-stability
---

Assume the group supplied by `cyclic-carrier-energy-stability` were
hyperlinear and choose canonical-delta microstates `U_n`. The finite moment
window defining `E` converges to the regular character, so

```text
E(U_n)->E_reg.
```

Their relator defects tend to zero, while `(CES)` gives

```text
limsup_n E(U_n)<=beta_fd<E_reg,
```

a contradiction. This criterion is strictly weaker than full matrix-only
cyclic invariance because `beta_fd` may be positive.
