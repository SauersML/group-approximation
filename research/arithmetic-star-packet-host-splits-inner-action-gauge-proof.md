---
rg: 2
id: arithmetic-star-packet-host-splits-inner-action-gauge-proof
kind: route
title: Untwist the inner semidirect action and read the commuting source copy
target: arithmetic-star-packet-host-splits-inner-action-gauge
requires:
  - arithmetic-star-packet-carrier
artifacts:
  - notes/ARITHMETIC_STAR_PACKET_HYPERLINEAR_AUDIT.md
---

For multiplication

```text
(x,p)(y,q)=(x theta(p)y theta(p)^(-1),pq),
```

the proposed map sends the product to
`(x theta(p)y theta(q),pq)`, which is the product of the two images in
`K times P`.  Its inverse is `(z,p)|->(z theta(p)^(-1),p)`.  The formulas for
the embedded source and `c_p` follow immediately.

