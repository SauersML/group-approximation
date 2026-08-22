---
rg: 2
id: verifier-controlled-two-cycle-loss-blind-proof
kind: route
title: Complete every verifier-controlled swap by a flag qubit
target: verifier-controlled-two-cycle-is-existentially-loss-blind
requires:
  - central-marked-two-cycle-zero-compression-cell
---

The positive localization statement is the established marked two-cycle cell
with `y=r`.  If `(VTL1)` holds, its source projection is

```text
(1-r)(1-z)/4=L(1-z)/2.
```

It remains to show that this creates no payment.  Let `R=E_+-E_-` and use
the Pauli involutions `X,Z` on a fresh flag qubit.  The operator `w` in
`(VTL4)` is a self-adjoint involution because the two spectral projections
are orthogonal.  It commutes with `R tensor 1`, while

```text
w(1 tensor Z)w
 =E_+ tensor Z+E_- tensor XZX
 =E_+ tensor Z-E_- tensor Z
 =R tensor Z.
```

Thus `(VTL2)` is exact.  Formula `(VTL5)` follows immediately, and `X`
maps the negative `Z`-line orthogonally to the positive `Z`-line, proving
`q w q=0`.

Since the construction works for every rank of `E_-`, its relation residual
has infimum zero at every prescribed losing mass.  Spectral rounding of an
approximately involutive unitary first replaces it by `R`; assigning the new
letters by `(VTL4)` then makes the new-cell defects zero relative to `R`, and
the fixed word substitutions change them by only the rounding error.  This
also rules out robust payment by the same cell.

