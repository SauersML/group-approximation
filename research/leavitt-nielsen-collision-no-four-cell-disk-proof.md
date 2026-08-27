---
rg: 2
id: leavitt-nielsen-collision-no-four-cell-disk-proof
kind: route
title: Contract the duplicate-gate digons and evaluate the unique four-cell residual face
target: leavitt-nielsen-collision-no-four-cell-disk
requires:
  - leavitt-nielsen-collision-has-a-hidden-first-side-relation
---

A four-cell paired picture is a connected planar cubic ribbon graph with two
positive and two negative vertices, six paired `z`-edges and four coefficient
regions.  The artifact enumerates the 2,620 reduced relator-colorings after
the ordinary opposite-relator dipole filter.

No coloring has the three internal identity regions required for a disk.
Exactly four colorings attain two internal identity regions, both supplied by
the folded `k_0=k_1=a_1` gate.  Up to cyclic rotation and inversion, the
third required internal label is

```text
u k^(-1) h x.
```

Using

```text
x=q_1a_0,  h=a_0p_1,  u=a_1,  k=p_0e_1q_0,
```

its coefficient expansion reduces to

```text
a_1 | q_0 | e_1 | (p^(-1)a)_0 | (pq)_1 | a_0.
```

Every displayed block is nonidentity and adjacent blocks lie in different
free factors.  This is an exact nonempty `G_0*G_1` normal form.  Hence the
collided candidate has no coefficient-kernel disk through four cells.
