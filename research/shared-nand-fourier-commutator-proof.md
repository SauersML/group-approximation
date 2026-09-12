---
rg: 2
id: shared-nand-fourier-commutator-proof
kind: route
title: Restrict the commutator to the forced NAND fiber and realize equality with Pauli matrices
target: shared-nand-fourier-commutator-is-separator-contaminated
requires: []
---

Because `S` commutes with `A`, the forbidden atom is

```text
e_- (1-A)/2=0.
```

Multiplication by two gives `e_-A=e_-`; the same argument applies to `B`.
This proves `(SNF2)--(SNF3)`.  If `[A,B]=-1`, multiplying by `e_-` gives
`e_-=-e_-`, hence `e_-=0` over `C`.

For sharpness, the matrices `(SNF6)` commute with `S` because the Hadamard
acts only on its two-dimensional plus eigenspace.  Direct spectral
calculation gives the three NAND atoms for both contexts.  The Pauli identity

```text
Z X Z X=-I_2
```

on the plus block and triviality on the minus line prove `(SNF7)`.  Hadamard
normalizes the finite Pauli group, so all displayed matrices lie in a finite
Clifford extension.  Finally, anticommuting involutions pair the plus and
minus eigenspaces of either one, so their carrier has even dimension; adding
the required nonzero separator-minus NAND atom proves the lower bound three.
