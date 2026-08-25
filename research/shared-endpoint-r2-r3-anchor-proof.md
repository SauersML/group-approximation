---
rg: 2
id: shared-endpoint-r2-r3-anchor-proof
kind: route
title: Cancel the common transporter or complementary split child
target: shared-endpoint-r2-r3-anchor-has-linear-seam-bound
requires: []
---

Unitary invariance and the triangle inequality applied to `(SEA1)` give

```text
||X-X'||_2
 =||P^*(X-X')P||_2
 <=||P^*XP-Q||_2+||Q-P^*X'P||_2
 <=2 eta.
```

For `(SEA3)`, right multiplication by `D^*` gives instead

```text
||X-X'||_2
 =||XD-X'D||_2
 <=||XD-C||_2+||C-X'D||_2
 <=2 eta.
```

Finally telescope `(SEA4)` and use right-unitary invariance:

```text
||Y-Y'||_2
 <=||Y-XR||_2+||(X-X')R||_2+||X'R-Y'||_2
 <=2 zeta+2 eta.
```

All constants are independent of the matrix dimension and of the size of
the surrounding Carmichael packet.

