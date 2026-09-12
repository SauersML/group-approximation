---
rg: 2
id: schur-parity-return-from-canonicalizable-negative-corner
kind: route
title: Canonicalize an arbitrary negative corner and apply the Schur density terminal
target: schur-amplified-parity-compressor-hs-return
requires:
  - toeplitz-parity-surviving-corner-is-canonically-regularizable
  - parity-compressor-old-commutant-has-positive-density
  - canonical-marked-corner-nonamenable-density-vanishes
---

Assume a marked model retains `J` and cut to its negative corner. Apply
`toeplitz-parity-surviving-corner-is-canonically-regularizable`. The
resulting marked sequence has canonical character on `Lambda` while
retaining `J=-1`.

The coefficient-covariant conclusion `(PCD1)` supplies a fixed positive
density of old low-commutator vectors on that sequence. This contradicts
the Kesten low-energy-density vanishing theorem. Hence the marked corner
cannot survive.
