---
rg: 2
id: unitary-k2m-rectangle-synchronization
kind: claim
title: K2,m unitary edge data synchronize exactly through m-1 rectangle holonomies
---

Let `m>=1` and let

```text
M_(i,j) in U(d),     i in {0,1},  j in {0,...,m-1},
```

be unitary labels on the edges of `K_(2,m)`.  For `j>=1` define the canonical
rectangle holonomy

```text
H_j = M_(1,j) M_(0,j)^* M_(0,0) M_(1,0)^*.
```

Then there are row and column unitary gauges

```text
A_0,A_1,B_0,...,B_(m-1) in U(d)
```

such that

```text
M_(0,j) = A_0 B_j                                for every j,
||M_(1,j)-A_1 B_j||_2 = ||H_j-1||_2              for j>=1,
M_(1,0) = A_1 B_0.
```

In particular

```text
sum_(i,j) ||M_(i,j)-A_i B_j||_2^2
 = sum_(j=1)^(m-1) ||H_j-1||_2^2.                 (K2M-SYNC)
```

Thus a `U(d)`-valued edge assignment on `K_(2,m)` is exactly row/column
factorizable iff its `m-1` fundamental rectangle holonomies are trivial, and
approximate rectangle flatness gives dimension-free approximate
factorization with constant `1`.

The statement is noncommutative: no commutation among the `M_(i,j)` is
assumed.
