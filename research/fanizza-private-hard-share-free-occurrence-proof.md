---
rg: 2
id: fanizza-private-hard-share-free-occurrence-proof
kind: route
title: Put each complete gauge-doubled Fanizza occurrence in a free Thompson orbit
target: fanizza-private-hard-share-is-point-stabilizer-local
requires:
  - gauge-doubling-gives-selector-flip-symmetries
  - context-local-schur-packet-marked-extension
  - fanizza-bad-atoms-have-symmetric-frames
  - thompson-free-occurrence-amalgam-preserves-contextuality
---

The Fanizza BCS and its predicate menu are finite, so adjoining its gauge
shares and finitely many context packet generators gives one finite
presentation `H`.  The symmetric-frame theorem supplies the finite private
hard-word menu.  Put copies `H_x` in the free occurrence amalgam.  Stabilizers
fix `H_x` pointwise, distinct copies have no commutator relations, and the
gauge-invariant logical products remain shared exactly where the original
single occurrence shares them.

The marked extension theorem supplies an exact representation of `H` after
amplification, and gauge covariantization balances every chosen private hard
share.  The free amalgam and its folding map preserve the common mark.  Hence
the point-stabilizer bridge compiler applies to the chosen hard word at every
site, while no off-site contextual commutation has been introduced.
