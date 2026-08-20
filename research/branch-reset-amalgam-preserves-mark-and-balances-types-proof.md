---
rg: 2
id: branch-reset-amalgam-preserves-mark-and-balances-types-proof
kind: route
title: Use amalgam normal form, Pauli character transitivity, and shared-overlap alignment
target: branch-reset-amalgam-preserves-mark-and-balances-types
requires:
  - branch-controlled-pauli-selector-reset
  - finite-schur-clifford-packet-flexible-hs-exactification
  - shared-overlap-controls-packet-multiplicity-vector
---

The normal-form theorem for a free product with amalgamation embeds both
factors when the edge maps are injective. Hence `G` embeds in `(BRA1)` and its
word `w` survives.

Fix `J=-1` and one value of `q`. The reset theorem supplies `k` Pauli pairs
whose diagonal half is `z_1,...,z_k`. The corresponding finite Heisenberg
algebra is `M_(2^k)`, so its unique spin module contains every joint
`z`-character exactly once. Tensoring by an arbitrary external multiplicity
shows that all those character multiplicities are equal. This proves item 2.

For an approximate representation, exactify the two fixed finite group tables.
Both corrections approximate the same original words on `D`. Apply the
shared-overlap multiplicity-vector theorem to their exact `D` restrictions.
The reset-side vector is exactly balanced by item 2, so the child-side vector's
weighted `L1` distance from the balanced cone is bounded by the two correction
losses, hence by `C sqrt(E)`. All groups and word lists are fixed, so `C` is
independent of matrix dimension and tape level.

