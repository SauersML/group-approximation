---
rg: 2
id: factoriality-does-not-finitize-leavitt-root-data-proof
kind: route
title: Compare the finite root-kernel proof with the diffuse regular root algebra
target: factoriality-does-not-finitize-leavitt-root-data
requires:
  - finite-root-algebra-forces-steinberg-triviality
---

The finite-dimensional proof simultaneously diagonalizes one root image in
`U(d)`.  There are at most `2^d` diagonal sign matrices, so the additive root
kernel has finite index.  Intersecting finitely many such kernels produces a
nonzero two-sided ideal, and simplicity finishes the proof.

In a finite factor, simultaneous diagonalization means only that the root
image lies in some abelian von Neumann algebra.  Such an algebra may be
diffuse and contain infinitely many involutions.  The canonical subgroup
algebra

```text
L((L,+)) <= L(St_n(L))
```

is the exact countermodel to the finiteness step.  Its Haar realization is
`L^infinity(dual(L,+))`, and the dual Haar measure is nonatomic.  The common
root kernel is zero by the root-faithfulness dichotomy.

This does not claim that every factorial character has diffuse root
restriction.  It proves the logically sufficient obstruction: factoriality
does not imply the finite/atomic hypothesis consumed by the coefficient
quotient argument, and the regular tracial model displays the missing case
exactly.
