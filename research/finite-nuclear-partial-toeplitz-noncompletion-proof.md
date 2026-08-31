---
rg: 2
id: finite-nuclear-partial-toeplitz-noncompletion-proof
kind: route
title: Use the anticommuting Pauli square to obstruct completion of partial Toeplitz data
target: finite-nuclear-quotient-does-not-complete-partial-toeplitz-data
requires:
  - finite-positive-definite-window-is-a-relative-corner-selector
  - operator-system-face-colimit-need-not-have-concrete-group-order
---

On `G=C2 x C2`, prescribe Pauli involutions `X` and `Z` on the two
generator edges. Every allowed one-edge Toeplitz face is positive. A full
positive-definite extension has a Stinespring dilation compressing two
commuting involutions to contractions `A,B` close to `X,Z`. If `eta`
is the larger normalized Hilbert--Schmidt error, compression leakage is at
most `sqrt(2 eta)` in each direction, whence

```text
2=||XZ-ZX||_2 <= 4 eta+2 sqrt(2 eta).
```

Therefore `eta>=(3-sqrt(5))/4`. Even `C*(G)=C^4` cannot complete this
facewise-positive partial table.
