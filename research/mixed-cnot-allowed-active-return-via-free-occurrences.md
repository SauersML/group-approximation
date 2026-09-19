---
rg: 2
id: mixed-cnot-allowed-active-return-via-free-occurrences
kind: route
title: HNN-transport the three affine active atoms into the next free occurrence
target: mixed-cnot-allowed-active-return
requires:
  - s3-active-complement-is-three-equal-scale-affine-atoms
  - s3-affine-hnn-transports-the-active-vector
  - packet-central-active-complement-reduces-shared-words
  - thompson-free-occurrence-amalgam-preserves-contextuality
  - context-local-schur-packet-marked-extension
  - branching-plus-first-hit-exits-forces-hs-floor
---

Use the free occurrence amalgam to make the old and fresh Fanizza logical
tuples independent without making them commute.  Attach the same six-generator
endpoint packet to both occurrences and HNN-identify only their affine endpoint
subgroups `<J,K,b>`.  The fixed endpoint covariance relators transport each of
the three active atoms and therefore their sum, with `(SAH3)` controlling the
approximate mass discrepancy.  The target complement reduces the fresh shared
words by `(PAC2)--(PAC4)`.

Every allowed endpoint character appears among the three active atoms, so the
exact return deletes no allowed model.  The HNN base embedding retains the
marked word.  Its image of the fourth atom is ignored by the definition of the
next analytic active carrier; the separately constructed Thompson site bridge
has already put one copy of that exit mass in the summable first-hit sector.
The BFE scalar proof permits this: it uses only the active/exit trace balance
and never assumes that an HNN image of the inactive atom is zero.

## Invalidated

This last inference is false.  The first-hit ledger also requires that the
next active carrier lie below the survivor prefix.  The independent pulse
has no relation with the returned endpoint chart, so the HNN image `A'` need
not lie below that prefix.  The exact countermodel is recorded in
`free-occurrence-hnn-return-does-not-preserve-first-hit-prefix`.
