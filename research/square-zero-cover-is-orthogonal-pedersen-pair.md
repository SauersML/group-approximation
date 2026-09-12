---
rg: 2
id: square-zero-cover-is-orthogonal-pedersen-pair
kind: claim
title: Square-zero ideal covers are exactly orthogonal Pedersen pairs
---

Let `A` be any C-star algebra and `b in A_+`.  The following are equivalent:

1. There is `x in A` with `x^2=0` and `b in Ideal(x)`.
2. There are `p,q in A_+` and `z in A` such that

```text
z*z=p,       zz*=q,       pq=0,       b in Ideal(p).
```

Thus the finite-packet fusion frontier is exactly the problem of constructing
one orthogonal Pedersen-equivalent pair whose common ideal covers the reserved
cutdown.
