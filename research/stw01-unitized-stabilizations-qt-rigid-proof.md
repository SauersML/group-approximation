---
rg: 2
id: stw01-unitized-stabilizations-qt-rigid-proof
kind: route
title: Apply the stable-ideal theorem to the scalar quotient and audit nonexactness
target: stw01-unitized-stabilizations-are-nonexact-qt-rigid
requires:
  - stw01-stable-ideal-extensions-force-qt-linearity
---

The ideal `I=D tensor K` is stable and `A/I ~= C`.  The stable-ideal theorem
shows that every bounded 2-quasitrace `tau` on `A` vanishes on `I` and
factors through the scalar quotient.  A bounded positive 2-quasitrace on
`C` is `lambda id_C` for `lambda>=0`, proving `(US2)`.  Conversely every
such multiple of `pi` is a trace, including the nonzero choice `lambda=1`.

Separability and unitality are immediate from `(US1)`.  If `A` were exact,
then its closed ideal `I` would be exact.  Exactness is Morita invariant, so
the full corner `D tensor e_11 ~= D` would be exact, contrary to the choice
of `D`.  Hence `A` is nonexact.
