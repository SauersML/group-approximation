---
rg: 2
id: reynolds-pauli-exit-firewall-proof
kind: route
title: Compare the Reynolds used range with the native dressed commutator
target: reynolds-exit-does-not-carry-pauli-gauge
requires:
  - index-two-reynolds-hnn-is-a-proper-corner-section
  - same-range-dressed-reynolds-sections-expose-raw-source-unitary
  - controlled-pauli-commutator-is-and-times-multiplicity-commutator
---

The Reynolds support identities give `(REG1)--(REG3)` and make `E_exit`
orthogonal to every same-range dressed path.  Direct word reduction using
`(CPM5)` gives `(REG4)`, while the sector formula `(CPM6)` gives the
independent check `(REG5)`.  Hence neither the recovered source unitary nor
the packet-dressed commutator acts as a pure gauge on the exit, establishing
the claimed scoped obstruction.
