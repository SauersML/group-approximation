---
rg: 2
id: toeplitz-schur-bcs-shift-amalgam-proof
kind: route
title: Combine diagonal clocks, local marked packets, and the child-MASA tail recurrence
target: toeplitz-schur-bcs-shift-amalgam
requires:
  - diagonal-covariance-synchronizes-hnn-and-bcs-shifts
  - diagonal-covariance-has-quadratic-hs-word-cost
  - context-local-schur-packet-marked-extension
  - schur-child-toeplitz-morita-wire
  - oriented-schur-child-branching-identity
  - toeplitz-schur-child-masa-recurrence
  - uniform-relative-clifford-tape-cell
---

Use distinct shifts `t,U` and the finite diagonal covariance relations. The
first two prerequisites give every level input word and a quadratic
derivation bound. Extend the exact marked BCS representation by all finite
context packets using the third prerequisite.

Place each packet diamond across the Toeplitz head/tail boundary. The Morita
wire identifies its doubled restriction multiplicity with the two transverse
child commutants rather than with a scalar word or an isomorphic HNN edge.
The child-MASA recurrence makes the compressed child the next input carrier,
charges the inactive Fanizza terms, and preserves the exact marked extension.
Uniform relative-cell rounding supplies a level-independent analytic modulus;
only the permitted polynomial word cost remains. These statements give all
five clauses of the target.
