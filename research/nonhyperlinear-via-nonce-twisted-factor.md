---
rg: 2
id: nonhyperlinear-via-nonce-twisted-factor
kind: route
title: Form the countable phase-range central extension of a bad twisted factor
target: non-hyperlinear-group
requires:
  - non-ce-twisted-group-factor-exists
  - nonce-twisted-factor-gives-nonhyperlinear-group
---

Choose `Gamma,omega` from `non-ce-twisted-group-factor-exists` and form the
countable central extension

```text
<range(omega)> x_omega Gamma.
```

The compiler `nonce-twisted-factor-gives-nonhyperlinear-group` proves that
this explicit extension is nonhyperlinear.

