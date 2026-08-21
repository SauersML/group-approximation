---
rg: 2
id: nonhyperlinear-from-matrix-only-cyclic-carrier-invariance
kind: route
title: Contradict the canonical Kazhdan carrier floor with finite-matrix invariance
target: non-hyperlinear-group
requires:
  - matrix-only-cyclic-carrier-invariance
  - infinite-conjugacy-orbits-give-canonical-carrier-no-capture
---

Assume `G` were hyperlinear and choose canonical-delta microstates `U_n`.
The relator defect tends to zero, so `(MCI1)` makes the commutator energy of
`f(U_n(w))` tend to zero. Canonical moment convergence and
`infinite-conjugacy-orbits-give-canonical-carrier-no-capture` give the fixed
positive lower bound

```text
kappa sum_(k!=0)|c_k|^2>0.
```

This contradiction proves that `G` is non-hyperlinear.
