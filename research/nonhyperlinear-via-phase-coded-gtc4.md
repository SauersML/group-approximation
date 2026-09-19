---
rg: 2
id: nonhyperlinear-via-phase-coded-gtc4
kind: route
title: Authenticate the marked BCS cuts by phase fingerprints and apply the global decoder
target: non-hyperlinear-group
requires:
  - oracularizable-tracial-nonru-game-exists
  - dihedral-spin-packet-supplies-common-partial-swap
  - common-source-partial-isometries-decode-one-game-state
  - global-marked-type-cycle-selector-decoder
  - compressed-k2m-deficit-is-one-aggregate-sign-row
  - normalizer-phase-tests-leave-diagonal-type-transport
  - phase-covariance-words-exactly-measure-type-transport-leakage
  - phase-tagged-row-defect-reduces-to-within-type-selector-mismatch
  - finite-phase-codewords-weight-type-gram-leakage
  - spectral-compressed-leakage-is-finite-word-moment-functional
  - finite-phase-tags-authenticate-forbidden-cuts
  - forbidden-weighted-type-carrier-coverage-is-rank-rounding
  - marked-corner-cycle-needs-no-full-mass-concentration
---

The source and common partial-swap front end give one shared non-CE BCS state
and exact completeness with a surviving common central mark.  Rank trimming
covers the forbidden mass inside its negative corner.  Authenticated
word-spectral type tags and their phase-matching covariance rows exactly
remove wrong-type population; the Fourier codeword identity removes off-type
Gram coherence.  The remaining open claim is only the within-type
forbidden-selector comparator.  By
`phase-tagged-row-defect-reduces-to-within-type-selector-mismatch`, that
comparator supplies the complete matrix-only row domination `(GTC4)`.

`marked-corner-cycle-needs-no-full-mass-concentration` applies the robust BCS
gap directly on that corner, so no comparison with unmarked forbidden mass
is needed.  The resulting fixed ordinary relator-energy floor contradicts
canonical hyperlinear microstates, while exact completeness keeps the mark
nontrivial.
