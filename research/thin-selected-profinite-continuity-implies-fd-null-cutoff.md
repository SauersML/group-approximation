---
rg: 2
id: thin-selected-profinite-continuity-implies-fd-null-cutoff
kind: route
title: Whole-module finite-dimensional continuity controls the universal cutoff sequence
target: thin-selected-fd-null-cutoff-cannot-survive-matrices
requires:
  - thin-selected-module-is-profinite-continuous
  - thin-leak-has-universal-fd-null-laplacian-witness
---

Weak containment of the selected cyclic module in `pi_FD^0` gives

```text
||alpha(y_N)|_(K_v)|| <= ||y_N||_FD <= 2q^N.            (1)
```

The vector `(1-P_A)v` lies in `K_v`, while `y_N` kills the `A`-fixed part.
Thus `(1)` bounds `||alpha(y_N)v||_2` by `2q^N`, proving `(SFC1)`.
