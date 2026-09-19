---
rg: 2
id: native-a2-average-fourier-support-proof
kind: route
title: Separate the two path average into two lamp double cosets
target: native-a2-two-path-average-is-not-an-ordinary-word-compression
requires:
  - first-root-parahoric-target-has-a-distinct-double-coset-type
  - two-path-holonomy-is-paid-by-corner-leakage
  - single-group-word-compression-unitary-normalizes-corner
---

Equation `(NTA4)` identifies the relative holonomy with `d`.  Canonical
regular trace kills both `d` and `cd`, giving `(NTA5)` and hence `(NTA6)` by
the established positive-Gram identity.

For the wordization fence, expand `P rho(g)P` in the group basis.  Every
term lies in `<c>g<c>`.  The required target has nonzero coefficients at the
identity and at `d`.  Containing the identity forces `g in<c>`, whose double
coset is `<c>` and cannot contain `d`.  Therefore no group word has the
required compression.

