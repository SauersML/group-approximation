---
rg: 2
id: zpc-reynolds-exit-authenticates-identity-copy
kind: route
title: Use the index-two Reynolds exit as the identity-copy gauge carrier
target: zpc-active-identity-copy-mixed-occurrence-on-a-positive-corner
requires:
  - index-two-reynolds-hnn-is-a-proper-corner-section
  - same-range-dressed-reynolds-sections-expose-raw-source-unitary
  - controlled-pauli-commutator-is-and-times-multiplicity-commutator
---

**INVALIDATED EXISTING-SECTION SHORTCUT.**  The proposed construction names
the active assignment mass as the unused range of the index-two Reynolds
section and tries to read the active controlled-Pauli gauges there by
same-range dressing.

`reynolds-exit-does-not-carry-pauli-gauge` proves that the dressings recover
their relative unitary on the source `p`, while the assignment mass lies in
the orthogonal unused range `q-vv^*`.  Native dressing also fails:
`[XU,ZV]=JST[U,V]` retains only an affine selector phase after the original
commutator relation.  A second section sourced on the exit, or a genuinely
new exit-based mixed Gram, is required.
