---
rg: 2
id: sl3-fdg-via-generator-diagonal-root-leak
kind: route
title: Charge the distinguished generator diagonal directly with the localized root leak
target: sl3-hnn-finite-window-central-dual-gap
requires:
  - generator-diagonal-is-a-central-matrix-range-separator
  - unbalanced-torus-word-localizes-britton-leak
---

**INVALIDATED PROPOSAL.**  If the lattice tuple is a positive distance from
its ucp matrix range, take the distinguished separator

```text
B_s=X_s/sqrt(|S|).
```

It is stable-letter-central and has a positive gap by
`generator-diagonal-is-a-central-matrix-range-separator`.  Attempt to use
the fixed root defect from
`unbalanced-torus-word-localizes-britton-leak`, together with the fact that
the same `X_s` occur in the separator, to force its support function upward.

`generator-diagonal-does-not-couple-to-root-leak` gives an exact
four-dimensional countermodel to every argument using only these local
data.  Its entire selected tuple commutes with the stable letter, the
unbalanced word and one-Britton inputs are exact, the named root defect is
maximal, and the distinguished generator diagonal itself has a positive
gap with aligned off-spectral mass.  Therefore its special form supplies no
formal coupling.  A viable proof must use additional approximate `SL_3`
relations to construct the ucp comparison point.
