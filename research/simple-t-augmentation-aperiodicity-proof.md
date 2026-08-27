---
rg: 2
id: simple-t-augmentation-aperiodicity-proof
kind: route
title: Pass finite character orbits to augmentation coinvariants
target: simple-t-augmentation-module-is-aperiodic
requires: []
---

A finite orbit gives a finite-index stabilizer.  Taking its core gives a
homomorphism from `A` to a finite symmetric group.  Simplicity makes its
kernel either trivial or all of `A`; it cannot be trivial because `A` is
infinite.  Thus the orbit is fixed.

Apply group homology to

```text
0 -> I_A -> F_2[A] -> F_2 -> 0.
```

The regular module has no positive homology and its coinvariants map
isomorphically onto `F_2`, leaving `(I_A)_A=H_1(A;F_2)`.  Perfectness kills
the latter.  Formula `(STA3)` proves finite module generation.
