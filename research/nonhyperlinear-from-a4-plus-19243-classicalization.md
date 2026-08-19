---
rg: 2
id: nonhyperlinear-from-a4-plus-19243-classicalization
kind: route
title: Collision-conditioned A4 classicalization rules out regular Leavitt microstates
target: non-hyperlinear-group
requires:
  - atlas-centralizer-products-19243-classicalize
  - atlas-a4-packet-centralizer-product-compiler
  - atlas-a4-19243-classical-collapse
  - leavitt-regular-atlas-separating-refinement
---

Suppose `Q=L_(F_2)(1,2)^x` were hyperlinear.  The regular-atlas refinement
produces relative unitaries `U_n` with all fixed atlas packet defects tending
to zero.  In particular the thirty shortest A4 pair-cubes and collision
`q_19243` have defect tending to zero.

The corrected centralizer-product compiler gives

```text
max_j dist_2(U_n,D_(j,k_n)) -> 0,
```

with the shifted sets `D_(j,k)` based at the fixed exact packet alignment `R`.
`atlas-centralizer-products-19243-classicalize` therefore gives

```text
dist_2(U_n,B_(k_n)) -> 0,
```

where `B_k` is the finite union of classical inner/outer packet alignment
cosets modulo the global regular-chart commutant.

But multiplication on the right by the global commutant does not change the
represented second chart, hence does not change the collision value.  By
`atlas-a4-19243-classical-collapse`, collision 19243 is a nonidentity regular
`A8` word on every classical packet branch.  Its normalized-HS distance from
`1` is therefore `sqrt(2)` on all of `B_k`.

Collision evaluation has four conjugated second-chart syllables, so for two
relative frames `U,V`, telescoping gives

```text
||q_19243(U)-q_19243(V)||_2 <= 8 ||U-V||_2.
```

Thus `dist_2(U_n,B_(k_n))->0` forces

```text
liminf ||q_19243(U_n)-1||_2 >= sqrt(2),
```

contradicting the atlas microstate condition
`||q_19243(U_n)-1||_2->0`.  Hence `Q` is nonhyperlinear.

This is the corrected replacement for the invalidated packet-only
centralizer-product route.  The collision belongs inside the classicalization
premise; the exhaustive GL5 screen proves that omitting it is false.
