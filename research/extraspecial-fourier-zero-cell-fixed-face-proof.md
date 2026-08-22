---
rg: 2
id: extraspecial-fourier-zero-cell-fixed-face-proof
kind: route
title: Compute the corrected shear and induce its fixed character
target: extraspecial-fourier-zero-cell-is-fixed-face-pruning
requires:
  - extraspecial-common-gauge-fourier-controller
  - finite-clifford-couplings-cannot-prune-a-forbidden-atom
---

Since `S` commutes with the Pauli packet, `(ESF2)` gives the first identity
in `(EFZ2)`.  Conjugate that identity once more by the involution `V`:

```text
X_i=(V U_i V^-1)(U_i X_i),
```

which gives `V U_i V^-1=U_i`.  Evaluation on a character of `(EFZ3)` now
gives `(EFZ4)`, and `a=0` is fixed exactly when `chi=0`, proving `(EFZ5)`.

The character `(EFZ6)` is invariant under `(EFZ2)`, hence defines a
one-dimensional representation of `<D,V>`.  In
`Ind_<D,V>^G(lambda)`, the identity-coset vector is fixed by the Reynolds
projection onto `X_i=1`, lies in the `J=-1` sector, and is fixed by `V`.
This proves `(EFZ7)`.  Centrality of `J` keeps the whole induced module in
the marked sector.

For the quotient alternative, a character descends through `D/N` exactly
when it is trivial on `N`.  The character `(EFZ6)` evaluates a word by its
`J` exponent after setting every `X_i,U_i` to one.  Its failure to descend is
therefore precisely an affine parity identification involving `J`.
