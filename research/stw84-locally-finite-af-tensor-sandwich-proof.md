---
rg: 2
id: stw84-locally-finite-af-tensor-sandwich-proof
kind: route
title: Sandwich the direct-product algebra between an AF tensor bound and the augmentation quotient
target: stw84-locally-finite-direct-factor-invariance
requires:
  - stw84-directed-union-uniform-bound
---

Exhaust `L` by finite subgroups.  Their group C*-algebras are finite
dimensional, so `stw84-directed-union-uniform-bound` shows that `C*(L)` is AF
and has nuclear dimension zero.  Equivalently, the increasing union of these
finite-dimensional group algebras is already a direct AF model.

Both groups are amenable, and the direct-product representation gives

```text
C*(L times H)=C*(L) tensor_min C*(H).                 (1)
```

The tensor-product estimate for nuclear dimension and
`dim_nuc(C*(L))=0` imply

```text
dim_nuc(C*(L times H)) <= dim_nuc(C*(H)).             (2)
```

The trivial character `epsilon_L:C*(L)->C` makes

```text
epsilon_L tensor id : C*(L times H) -> C*(H)
```

a surjective *-homomorphism.  Quotient monotonicity gives the reverse
inequality to (2).  If the right side is infinite, this quotient already
forces the left side to be infinite, so the argument covers all values.

