---
rg: 2
id: polar-compression-first-exit-proof
kind: route
title: Integrate the polar singular-value deficiency and telescope the raw words
target: polar-compression-turns-band-mismatch-into-first-exit
requires: []
---

Equation `(PCB5)` shows that every missing source vector contributes one to
`ell`, and `(1-s)^2<=1-s^2` bounds polar displacement by the same integral.
Equal trace of `P,Q` identifies the source and range deficiencies.  The two
terms in `(PCB6)` have orthogonal row supports, proving `(PCB4)`.

For a chain, replace `V_k` by `U_kP_(k-1)`, then `V_(k-1)`, and continue.
At each stage the product to the right already has range under the relevant
`P_i`, so the projection disappears and the error is at most
`sqrt(2ell_i)`.  This proves `(PCB8)`; the raw return defect gives `(PCB10)`.
