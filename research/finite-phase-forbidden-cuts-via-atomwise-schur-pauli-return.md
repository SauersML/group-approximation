---
rg: 2
id: finite-phase-forbidden-cuts-via-atomwise-schur-pauli-return
kind: route
title: Replace nonlinear forbidden cuts by coordinate atoms and named Schur Pauli flags
target: finite-phase-tags-authenticate-forbidden-cuts
requires:
  - coordinate-phase-atoms-remove-nonlinear-forbidden-union
  - every-forbidden-atom-has-fixed-schur-pauli-words
  - schur-pauli-words-name-atomwise-half-quarter-flags
  - atomwise-schur-pauli-cycle-return
---

Refine every marked forbidden/type carrier into its finitely many literal
assignment atoms.  Coordinate covariance words pay all transport between
different assignments, while the existing phase-code rows pay transport
between different packet types.  On each remaining atom, use the relative
and baseline Pauli words of the Schur packet to define the exact half and
quarter flags.  Their carrier traces sum to the full marked forbidden mass,
up to only the fixed packet exactification modulus.

The atomwise cycle-return estimate is then exactly `(WI1)` for this choice
of carriers.  Summing over the fixed finite atom menu proves
`finite-phase-tags-authenticate-forbidden-cuts`.  In particular the route no
longer asks one group word to compute a nonlinear Boolean characteristic
function; its only open input is the common multiplicity-reservoir return.

