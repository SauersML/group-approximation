---
rg: 2
id: nekrashevych-sign-tape-schur-lift
kind: route
title: Use twisted subtree squaring and adjoint mixing for the backward contraction ledger
target: finite-dimensional-schur-lift-of-doubling-tape
requires:
  - self-referential-bcs-doubling-tape
  - self-similar-central-sign-cocycle
  - nekrashevych-clifford-sign-tape
  - thompson-pauli-prefix-rounding-has-polynomial-cost
  - fanizza-schur-density-substitution
  - nekrashevych-violation-density-recurrence
  - contractive-computation-ladder
---

Place the Fanizza level-`n` cell on one binary cylinder and use the
partial-center reset to expose its corrected child branch as the next
Thompson Pauli coordinate. Internal conjugation gives identical addressed
HS cost, while coordinate-Pauli averaging exactifies only the new pair with a
polynomial depth loss.  The cocycle supplies the phase required to retain the
negative mark.

The violation-density claim resets the old selector chart and aligns the
returned child with the next Fanizza level.  Its balanced reset ray supplies a
fixed violation fraction, so `schur-violation-density-gives-contraction`
produces `(SDL2)` with some fixed coefficient `lambda<1`; polynomial
addressing and Pauli-channel costs are summable by
`contractive-computation-ladder`.  No sibling covariance assertion is used:
`schur-violation-density-is-in-the-spin-commutant` proves that such an
assertion cannot be obtained from a spin expander.  This route also does
**not** infer the recurrence from raw `tr(z_n)=tr(z_(n+1))^2`, which fails the
negative-sign sanity check.
