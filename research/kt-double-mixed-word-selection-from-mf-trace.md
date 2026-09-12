---
rg: 2
id: kt-double-mixed-word-selection-from-mf-trace
kind: route
title: An MF canonical trace supplies the mixed reduced-word models
target: kt-double-mixed-word-trace-selection
requires:
  - reduced-amalgam-canonical-trace-is-mf
  - kt-double-hyperlinear-iff-mixed-word-trace-selection
---

An MF approximation of the canonical trace on `C*(D)` is, after polar
rounding the images of the finitely many tested group unitaries, a canonical
normalized-Hilbert--Schmidt microstate sequence for `D`.  Hence `D` is
hyperlinear.  The forward implication of
`kt-double-hyperlinear-iff-mixed-word-trace-selection` then supplies
`(KMW1)--(KMW4)`.

This arrow is intentionally one-way.  Mixed-word selection asks only for
normalized-Hilbert--Schmidt models, whereas the prerequisite asks for an MF
trace with operator-norm multiplicativity.
