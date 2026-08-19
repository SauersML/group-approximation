---
rg: 2
id: unitary-k2m-rectangle-synchronization-proof
kind: route
title: Gauge one spanning tree and read every remaining edge as its rectangle holonomy
target: unitary-k2m-rectangle-synchronization
requires: []
---

Choose the gauges explicitly:

```text
A_i = M_(i,0),
B_j = M_(0,0)^* M_(0,j).
```

Then `B_0=1`, so

```text
A_0 B_j = M_(0,j)             for every j,
A_1 B_0 = M_(1,0).
```

For `j>=1`, unitary invariance of normalized Hilbert--Schmidt norm gives

```text
||M_(1,j)-A_1 B_j||_2
 = ||M_(1,j)-M_(1,0) M_(0,0)^* M_(0,j)||_2
 = ||M_(1,j) M_(0,j)^* M_(0,0) M_(1,0)^* - 1||_2
 = ||H_j-1||_2.
```

All edges in the first row and the distinguished edge `(1,0)` therefore have
zero error, and the only errors are exactly the `m-1` rectangle holonomies.
Squaring and summing proves `(K2M-SYNC)`.

If every `H_j=1`, the displayed gauges give exact factorization.  Conversely,
if `M_(i,j)=A_i B_j`, direct cancellation around every rectangle gives
`H_j=1`.  No commutativity is used anywhere.
