---
rg: 2
id: controlled-density-holonomy-via-v4-cross-gram
kind: route
title: Pay controlled Schur flip density through global V4 cross-Gram curvature
target: controlled-reset-needs-positive-density-holonomy
requires:
  - controlled-pauli-corner-has-clifford-groupification
  - clifford-groupified-control-is-forced-balanced
  - schur-packet-flips-realize-predicate-cocycle
  - full-v4-latent-coordinate-has-an-operator-five-fourths-floor
  - global-v4-exit-capacity-is-cross-gram-curvature
  - globally-conditioned-v4-exit-capacity
  - finite-depth-contractive-computation-ladder
---

Synchronize the three balanced controlled failures in the full V4 radical
packet.  Their exact operator sum has trace `5/4` of the forbidden parent.
Use the Pauli-completed covariance letters as the branch maps, and retain the
Schur flip square on their external multiplicity factors.

The global exit-capacity theorem bounds off-parent leakage plus cross-Gram
overlap by the shared-context relator energy.  The analytic curvature theorem
then forces at least one quarter of the forbidden parent mass to pay that
energy.  This is an amplification-stable density statement: it controls range
overlaps, not an integral multiplicity remainder.

Insert the resulting local payment into the fixed number of controlled
branch comparisons.  Fixed-packet exactification and the finite-depth ledger
absorb all square-root errors.  The global-use clause of
`globally-conditioned-v4-exit-capacity` is essential; applying the same
capacity independently to one packet would be the circular local
nonhyperlinearity theorem.

