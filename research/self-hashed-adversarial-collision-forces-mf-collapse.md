---
rg: 2
id: self-hashed-adversarial-collision-forces-mf-collapse
kind: claim
title: Uniformly self-hashed unbounded packet challenges force operator-norm collapse of the marked phase
distinct_from:
  opnorm-coordinatewise-capacity-diagonal: that is the abstract post-coordinate capacity theorem; this instantiates its soundness with finite unitary palettes and the packet collision estimate.
  authenticated-opnorm-challenge-compiler: that extensional compiler is already established by an MF-radical seed; this is a seed-free conditional matrix theorem for a specific finite self-hashing packet interface.
  hyperlinear-to-mf-saturation-compiler: that extracts and renormalizes a Kazhdan moving corner after tracial saturation; this proof uses operator norm directly and performs no corner renormalization.
artifacts:
  - research/artifacts/no-renormalization-adversarial-collision-compiler-2026-08-23.md
  - research/artifacts/finite-memory-self-hashing-non-mf-2026-08-23.md
  - GroupApproximation/Sofic/CollisionCapacityDetectors.lean
---

Let `Gamma=<S|R>` be finitely presented with marked word `z`. Suppose one
finite word interface exposes finite packet challenge graphs of unbounded
chromatic number, and every addressed local and edge check has operator-norm
defect at most

```text
C_0 Def_R(U)
```

with the same `C_0` at every challenge depth. Then every norm-matrix-corona
homomorphism kills `z`.

Indeed, if `z` remains separated by `eta`, freeze one sufficiently accurate
coordinate of dimension `d`. Choose, after seeing `d`, a challenge graph
beyond the finite `eta/8`-palette capacity of `U(d)`. Uniform self-hashing
makes its checks as accurate as the root checks. The monochromatic-edge
collision estimate then gives `||z-I||<eta`, a contradiction.

If an exact representation has `z!=1`, `Gamma` is non-MF. This theorem is
conditional only on the stated finite word interface; it does not assert that
the open compiler below has been constructed.
