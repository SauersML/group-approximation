---
rg: 2
id: self-hashed-adversarial-collision-forces-mf-collapse-proof
kind: route
title: Freeze one coordinate, choose its palette nemesis, and invoke the uniform capacity diagonal
target: self-hashed-adversarial-collision-forces-mf-collapse
requires:
  - finite-palette-packet-challenge-collapse
  - opnorm-coordinatewise-capacity-diagonal
artifacts:
  - research/artifacts/no-renormalization-adversarial-collision-compiler-2026-08-23.md
  - GroupApproximation/Sofic/CollisionCapacityDetectors.lean
---

Assume a corona image keeps the mark at operator distance at least `eta` on a
subsequence.  Pick one coordinate whose root defect is below the fixed
self-hash tolerance. Compactness supplies a finite palette of `U(d)` with
color diameter small enough that

```text
2 delta+2 C_0 Def_R(U)<eta.
```

Now choose a pre-existing challenge graph which defeats that palette. The
uniform self-hash controls every local and edge check in this same coordinate,
independently of its depth. `finite-palette-packet-challenge-collapse` forces
the mark below `eta`, contradiction. This is exactly the post-coordinate
choice licensed by `opnorm-coordinatewise-capacity-diagonal`.
