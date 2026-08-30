---
rg: 2
id: stw84-locally-finite-lamp-wreath-bound
kind: claim
title: Locally finite-lamp wreath products over uniformly bounded locally virtually nilpotent groups have finite nuclear dimension
---

Let `L` be a countable locally finite group and let `H` be a countable group
such that every finitely generated subgroup of `H` is virtually nilpotent.
Suppose that

```text
sup{h(V): V subset H finitely generated}=r<infinity.
```

For the restricted wreath product

```text
L wr H = (direct_sum_H L) rtimes H
```

one has

```text
dim_nuc(C*(L wr H)) <= 2 * 9^(r^2) < infinity.          (1)
```

If `r=0`, then `L wr H` is locally finite and the sharper value is zero.
Neither commutativity nor a uniform bound on the orders of the finite
subgroups of `L` is required.

For example, with `L=direct_sum_N A_5` and `H=(Q,+)`, formula (1) gives the
bound `18`.  This group has an infinite nonabelian locally finite lamp group
and is not locally virtually polycyclic.
