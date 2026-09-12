---
rg: 2
id: zpc-freezing-via-standard-form-right-copy
kind: route
title: Move the readable algebra to the right action and read off a commuting frozen strategy
target: zpc-readable-control-freezing-to-lcs
requires:
  - zpc-readable-variables-global-boolean-field
  - standard-form-side-switch-gives-commuting-frozen-strategy
---

Represent the perfect ZPC-IRS strategy on the standard form `L^2(M,tau)`,
keep the unreadable observables in the left action, and replace each joint
readable spectral projection by its right-action copy.  The right copy
commutes with every left unreadable observable and preserves the one-vector
correlation, so the proposed shortcut read off a perfect commuting-operator
strategy for the frozen system without ever exhibiting an invariant readable
atom.

This route is invalid.  The side switch produces two mixed player algebras
that commute only when the readable controls already commute with every
unreadable observable, so it assumes the frozen-fibre hypothesis rather than
supplying it; see
`standard-form-right-copy-does-not-freeze-zpc-controls`.
