---
rg: 2
id: one-bit-clifford-selector-half-proof
kind: route
title: Flip the selector spectrum on the marked assignment atom
target: one-bit-clifford-selector-halves-a-chosen-bcs-atom
requires: []
---

For involutions, the commutator convention gives
`[p,q]=pqpq`.  On `E_(c,a)`, `(OCS1)` therefore says `pqpq=-1`, equivalently
`q p q=-p`.  Since `q` commutes with `E_(c,a)`, it conjugates
`E_(c,a)(1+p)/2` onto `E_(c,a)(1-p)/2`.  The two projections are orthogonal
and sum to `E_(c,a)`, proving `(OCS3)`.

In the approximate setting, involution rounding and block-diagonalization
against the finitely many context commutators cost `O(sqrt(E))` in normalized
Hilbert--Schmidt norm.  Alternatively, after rounding `p`, conjugacy and
traciality give directly

```text
2|tau(E_(c,a)p)|
 <=||q E_(c,a)p q+E_(c,a)p||_2
 <=C sqrt(E).
```

Expanding `(1+p)/2` proves `(OCS4)`.  The two Pauli blocks in `(OCS5)` give
commutator `+1` on `e_+` and `-1` on `e_-`, hence `[p,q]=e_+-e_-=z`.

