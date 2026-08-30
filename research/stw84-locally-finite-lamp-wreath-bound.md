---
rg: 2
id: stw84-locally-finite-lamp-wreath-bound
kind: claim
title: Uniform local polynomial growth bounds the dimension of locally finite-lamp wreath products
---

Let `L` be a countable locally finite group and let `H` be a countable group
such that every finitely generated subgroup `V subset H` has polynomial
growth.  Write `d(V)` for its polynomial-growth degree, with `d(V)=0` when
`V` is finite, and suppose

```text
D=sup{d(V): V subset H finitely generated}<infinity.
```

For the restricted wreath product

```text
L wr H = (direct_sum_H L) rtimes H
```

one has

```text
dim_nuc(C*(L wr H)) <= 2 * 9^D < infinity.              (1)
```

If `D=0`, then `L wr H` is locally finite and the sharper value is zero.
Neither commutativity nor a uniform bound on the orders of the finite
subgroups of `L` is required.

By Gromov's theorem, the local polynomial-growth hypothesis is equivalent to
local virtual nilpotence.  If instead it is recorded by the uniform local
Hirsch bound

```text
sup{h(V): V subset H finitely generated}=r<infinity,
```

then `d(V)<=h(V)^2` gives the earlier estimate

```text
dim_nuc(C*(L wr H)) <= 2 * 9^(r^2).                    (2)
```

For example, with `L=direct_sum_N A_5` and `H=(Q,+)`, one has `D=1`, so (1)
gives the bound `18`.  This group has an infinite nonabelian locally finite
lamp group and is not locally virtually polycyclic.
