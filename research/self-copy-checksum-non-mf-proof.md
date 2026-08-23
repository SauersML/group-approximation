---
rg: 2
id: self-copy-checksum-non-mf-proof
kind: route
title: Upgrade the exact self-copy compression detector to an MF obstruction
target: finite-memory-self-hash-non-mf
requires:
  - compression-defect-dies-in-finite-dimensions
  - self-copy-kadison-kastler-checksum
artifacts:
  - research/artifacts/finite-memory-self-hashing-non-mf-2026-08-23.md
---

The exact compression theorem identifies the marked sibling commutator killed
by every finite-dimensional representation.  The checksum supplies the missing
uniform operator-norm passage from an approximate HNN tuple to the same
finite-dimensional commutant pinning.  If a corona image kept the mark
separated, freeze one sufficiently accurate coordinate; the checksum would put
the sibling pair near the center of the parent algebra and force its commutator
near `1`, a contradiction.
