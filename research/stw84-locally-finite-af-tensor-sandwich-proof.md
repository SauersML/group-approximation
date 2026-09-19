---
rg: 2
id: stw84-locally-finite-af-tensor-sandwich-proof
kind: route
title: Sandwich the direct-product algebra between an AF tensor bound and the augmentation quotient
target: stw84-locally-finite-direct-factor-invariance
requires:
  - stw84-directed-union-uniform-bound
  - zero-dimensional-character-factor-preserves-nuclear-dimension
---

Exhaust `L` by finite subgroups.  Their group C*-algebras are finite
dimensional, so `stw84-directed-union-uniform-bound` shows that `C*(L)` is AF
and has nuclear dimension zero.  Equivalently, the increasing union of these
finite-dimensional group algebras is already a direct AF model.

Both groups are amenable, and the direct-product representation gives

```text
C*(L times H)=C*(L) tensor_min C*(H).                 (1)
```

The trivial representation gives a character `epsilon_L:C*(L)->C`.
Apply `zero-dimensional-character-factor-preserves-nuclear-dimension` to
`A=C*(L)` and `B=C*(H)` in (1).  It gives the claimed equality, including
when `C*(H)` has infinite nuclear dimension.
