---
rg: 2
id: property-t-free-existence-via-jacobson-shift-gap
kind: route
title: Use the explicit recursive Jacobson group and a positive three-word matrix gap
target: nonhyperlinear-property-t-free-explicit-mf-witness
requires:
  - jacobson-stable-letter-closes-boundary-recursion
  - jacobson-shift-gap-characterizes-mark-collapse
  - jacobson-shift-mixed-gap
artifacts:
  - research/artifacts/jacobson-stable-letter-recursion-and-matrix-gap-2026-09-08.md
---

The target asks for an explicit countable group with a nontrivial
MF-invisible mark; it does not require nonhyperlinearity. The first
prerequisite supplies the explicit finitely presented group
`Theta_shift` and its nontrivial head involution `w=x_13,Q`.
The second proves that positive `gamma_shift` is exactly collapse
of this mark in every norm matrix corona. The third is the still
open uniform positivity premise. Together they would prove

```text
1!=w in Rad_MF(Theta_shift).
```

The established algebraic and lifting steps use explicit finite
groups, a bilateral linear action, finite-group averaging, polar
decomposition, and fixed-word norm estimates. No property-`(T)`
input or estimate for almost invariant vectors of an infinite
subgroup is used. Exact recursion alone does not discharge the
positivity prerequisite.
