---
rg: 2
id: binary-jacobson-opnorm-square-decoder-proof
kind: route
title: Apply the sparse square-Toeplitz operator-norm gap to the selected Jacobson carrier
target: binary-jacobson-steinberg-head-root-is-mf-invisible
requires:
  - binary-jacobson-head-root-has-opnorm-square-decoder
  - positive-toeplitz-head-is-square-defect-or-rectangular-escape
---

**VALID IMPLICATION; INVALIDATED AS A REDUCTION.**  The argument below is
correct.  However,
`binary-jacobson-typed-square-decoder-is-still-target-equivalent` proves that
its first prerequisite, with its current quantifiers, is equivalent to this
route's target.  It therefore supplies no independent path to the target and
is invalidated in the research graph pending a nonvacuous occurrence-level
replacement.

Assume a norm-corona homomorphism of `Gamma_T` does not kill `w_T` and take
coordinate lifts on a finite presentation.  After a subsequence, the mark
has a nonzero operator-norm spectral cut.  The first prerequisite supplies
`C_n,P_n,X_n,Y_n` satisfying `(JSD1)`.

Work in the square corner `C_n M_(d_n)(C) C_n`, whose identity is `C_n`.
Set

```text
delta_n=||Y_nX_n-C_n||_op,       eta_n=||P_n-(C_n-X_nY_n)||_op.
```

The sparse clause `(PTH2-op)` of the second prerequisite gives, for all
large `n`,

```text
1=||P_n||_op <= eta_n+delta_n/(1-delta_n).
```

The right side tends to zero, a contradiction.  Hence every norm-corona
homomorphism kills `w_T`.
