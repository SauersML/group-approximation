---
rg: 2
id: stw78-central-matrix-folding-proof
kind: route
title: Multiply commuting central matrix units by the amplified relative witness
target: stw78-central-matrix-folding-descends-proper-infiniteness
requires: []
artifacts:
  - research/artifacts/stw78-finite-quasitrace-seed-audit-2026-08-30.md
---

Let `rho:M_n->A_infinity intersect A'` be unital and apply `phi`
coordinatewise.  This gives a unital homomorphism

```text
rho_phi:M_n -> B_infinity intersect phi(A)'.
```

For `c in C`, every constant sequence `c` commutes with every coordinate
`phi(a)` used to represent `rho`, because `C subset phi(A)'`.  Hence the
ranges of `rho_phi` and the constant copy of `C` commute.  Multiplication
therefore induces a unital homomorphism

```text
M_n tensor_max C -> B_infinity intersect phi(A)'.       (MF1)
```

The finite-dimensional first factor is nuclear, so the source in `(MF1)` is
canonically `M_n(C)`.  Proper infiniteness of its unit supplies two
isometries `v_1,v_2` with orthogonal ranges.  Their images under `(MF1)` are
still two orthogonal isometries with initial projection one.  Thus the unit
of `B_infinity intersect phi(A)'` is properly infinite.  The exact
central-isometry criterion gives O-infinity-stability of `phi`.

No injectivity of `(MF1)` is needed: the defining orthogonal-isometry
relations are preserved by every unital homomorphism.
