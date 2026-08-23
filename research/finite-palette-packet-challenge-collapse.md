---
rg: 2
id: finite-palette-packet-challenge-collapse
kind: claim
title: A high-chromatic authenticated packet challenge exceeds every fixed finite-dimensional palette
distinct_from:
  bounded-area-high-chromatic-conjugacy-collapse: that colors a conjugacy orbit in normalized Hilbert--Schmidt metric and derives tracial word collapse; this colors arbitrary packet states in operator norm and applies the twisted packet collision detector.
artifacts:
  - research/artifacts/no-renormalization-adversarial-collision-compiler-2026-08-23.md
  - GroupApproximation/Sofic/NoRenormalizationCapacity.lean
---

Fix a finite palette whose color classes have operator-norm diameter at most
`delta`.  If a finite challenge graph defeats every coloring by that palette,
then any assignment of packet states `B_v` contains an adjacent pair with

```text
||B_v-B_w||_op <= delta.
```

If every vertex also satisfies the twisted local packet relation and every
edge satisfies the cross commutation relation with error `epsilon`, then

```text
||Z-I||_op <= 2 delta+2 epsilon.
```

For a fixed finite matrix dimension, compactness of `U(d)` supplies such a
finite palette. Hence challenge graphs of unbounded chromatic number force
phase collapse in that dimension. The palette form is machine-checked as
`phase_close_of_palette_overflow`.
