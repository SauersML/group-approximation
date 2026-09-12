---
rg: 2
id: toeplitz-schur-bcs-shift-amalgam-corrected-proof
kind: route
title: Combine diagonal clocks with corrected child-branch flips and selector recurrence
target: toeplitz-schur-bcs-shift-amalgam
requires:
  - diagonal-covariance-synchronizes-hnn-and-bcs-shifts
  - diagonal-covariance-has-quadratic-hs-word-cost
  - context-local-schur-packet-marked-extension
  - schur-child-toeplitz-morita-wire
  - oriented-schur-child-branching-identity
  - schur-child-center-sign-flip-is-group-automorphism
  - hnn-selector-chart-transport-preserves-mark-and-types
  - toeplitz-schur-child-masa-recurrence
  - uniform-relative-clifford-tape-cell
---

Use distinct shifts `t,U` and the finite diagonal covariance relations.  The
first two prerequisites give every level input word and a quadratic
derivation bound.  Extend the exact marked BCS representation by all finite
context packets using the third prerequisite.

Place each packet diamond across the Toeplitz head/tail boundary.  The Morita
wire identifies its doubled restriction multiplicity with the two transverse
child commutants.  Do not use raw `q_*` spectral projections as child labels.
Instead, the finite semidirect child extension implements
`q_*->Jq_*`, which sends the corrected center `Q_f->JQ_f` and pairs the two
actual child-simple types.  The child-MASA recurrence must then reset or
transport the remaining old selector character, make the compressed child
the next input carrier, charge the inactive Fanizza terms, and preserve the
exact marked extension.

Uniform relative-cell rounding supplies a level-independent analytic modulus;
only the permitted polynomial word cost remains.  These statements give all
five clauses of the target.  This route supersedes the raw-branch reset used
in the invalidated earlier route; it does not claim that the corrected center
itself is a group word.
