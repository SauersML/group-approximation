---
rg: 2
id: steinberg-zero-marginal-via-x-dual-surjectivity
kind: route
title: Kill zero-marginal chord solutions using the X row alone
target: steinberg-zero-marginal-fox-recurrence-is-zero
requires:
  - steinberg-zero-marginal-space-is-biaffine-circulation
  - steinberg-x-plus-incidence-dual-is-surjective
---

If `P=H=0` and both Fox recurrences hold, then in particular
`D(f)=X_ch(f)=0`.  The dual surjectivity `(SXD1)` is equivalent by
finite-dimensional duality to injectivity of the stacked map `(X_ch,D)`,
so `f=0`.  This route deliberately asks for the stronger X-only statement;
the `Y` row remains available if `(SXD1)` fails.
