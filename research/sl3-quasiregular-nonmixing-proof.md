---
rg: 2
id: sl3-quasiregular-nonmixing-proof
kind: route
title: Use finite-index intersections and a weakly null sequence in one intersection
target: sl3-lattice-inclusion-is-quasiregular-not-mixing
requires: []
---

Every `a in SL_3(Z[1/2])` commensurates `C`: clearing its finitely many
dyadic denominators shows that

```text
C_a=C cap a^(-1) C a
```

contains a principal congruence subgroup of `C`, and the conjugate
intersection has the same property.  Hence both relevant indices are
finite.  The standard group-factor calculation identifies

```text
closure(N u_a N)
```

with the correspondence induced from `L(C_a)`, so it has finite left and
right Jones dimension.  Since the `u_a` generate `M`, the quasi-normalizer
generates `M`.

For nonmixing take `a=h`.  The group

```text
P=C cap h^(-1) C h
```

is finite index and infinite.  Choose distinct `p_j in P` escaping every
finite subset and put `v_j=u_(p_j)`.  Then `v_j -> 0` weakly in `N`.  With
`x=u_h` and `y=u_(h^(-1))`, both outside `N`,

```text
x v_j y=u_(h p_j h^(-1)) in N,
```

so its conditional expectation has normalized `L^2` norm one.  This is the
negation of mixing.

