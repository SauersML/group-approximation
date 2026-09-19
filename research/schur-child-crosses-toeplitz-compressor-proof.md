---
rg: 2
id: schur-child-crosses-toeplitz-compressor-proof
kind: route
title: Scale a faithful class-two unitriangular model by the head and first-tail idempotents
target: schur-child-crosses-toeplitz-compressor
requires:
  - toeplitz-head-tail-unital-self-embedding
  - predicate-rank-gate-doubles-restriction-multiplicity
---

Write the packet in normal form using vector spaces over `F_2`,

```text
P=<p_1,...,p_m>,       Q=<q_1,...,q_m>,       Z=<J,z_1,...,z_k>,
beta:P x Q -> Z,
```

where `beta(p_i,q_j)` is the central commutator prescribed by the affine
matrix. On

```text
V=F_2 direct_sum Q direct_sum Z direct_sum P
```

the matrices

```text
g(p,q,z)=
  [ 1    0    0    0 ]
  [ q    I    0    0 ]
  [ z   B_p   I    0 ]
  [ p    0    0    I ],               B_p(q')=beta(p,q'),      (1)
```

form a faithful lower-unitriangular copy of `B_f`: multiplication contributes
the sole cross term `B_p q'=beta(p,q')`, and the last block records `p` even
when `beta` has a radical.

Now work over `T`. Put `e=xy` and `e_1=xfy=sigma(f)`. In `(1)` scale every
`q`- and `z`-coordinate by `e_1`; scale every baseline `p_i`-coordinate and
its `B_p` block by `1`; and scale the distinguished extra coordinate
`p_(N+1)` and its `B_p` block by `e`. The only multiplication check is

```text
1 e_1=e_1,                 e e_1=e_1.                         (2)
```

Hence the same packet multiplication table is realized over `T`. The storage
blocks and `e,e_1!=0` make the representation faithful. Unitriangular
matrices are products of elementary matrices, so the image lies in some
`EL_r(T)`.

Every generator of `B_f^Q` uses only coefficients `0,1,e_1`, all in
`sigma(T)`. The extra `p_(N+1)` has a storage entry equal to `e`, and
`e notin sigma(T)`, so it is not an entrywise `sigma`-matrix. This proves
`(SCT1)`.

Entrywise `sigma` is injective on matrices and sends elementary generators
onto the elementary group over the image subring, giving `(SCT2)` and
properness. The standard universal-lattice property-`(T)` theorem applies to
`EL_r(T)` once `r>=3`, because `T` is a finitely generated unital associative
ring. Enlarge the already fixed matrix size to that range.

