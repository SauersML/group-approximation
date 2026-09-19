---
rg: 2
id: centralizer-hnn-free-wreath-proof
kind: route
title: Send each conjugate stable letter to its coset-indexed free factor
target: centralizer-hnn-is-free-generalized-wreath
requires: []
---

Let

```text
W=( *_(x in A/C)<z_x> ) rtimes A,
a z_x a^(-1)=z_(ax).                                         (1)
```

The identity on `A` and `t->z_C` define `G->W`, because every `c in C`
fixes the base coset.  Conversely define

```text
z_(aC) -> a t a^(-1).                                        (2)
```

If `aC=a'C`, write `a'=ac`; the centralizer relations make the two values
in `(2)` equal.  The universal property of the free product extends `(2)`
to its lamp group, and conjugation by `A` obeys `(1)`.  The resulting map
`W->G` is inverse to the first map on `A`, `t`, and every lamp generator.
