---
rg: 2
id: leavitt-d3-length9-compound-holonomy-is-absent
kind: claim
title: The first two-unary compound holonomy packet has no cyclic realization
artifacts:
  - research/leavitt-d3-length9-compound-holonomy-is-absent-proof.md
  - research/artifacts/search-degree3-omega-four-cycle.py
distinct_from:
  leavitt-degree3-algebraic-corner-cycle-is-absent: that treats length eleven with the original seven-letter packet and four identities; this treats the smaller length-nine two-unary topology and the compound order-mismatch gates u=ab and v=cd.
---

Put `u=ab` and `v=cd` in the Leavitt coefficient group.  Then

```text
u^2=1,                         v^2=[c,d]=h!=1.
```

For every degree-three length-nine sign topology of orbit-valence type
`(1,1,7)` and every placement of the full-generating compound packet

```text
(u,u,v,v,r,e,p,a,c),
```

neither unary pivot makes the other unary relator trivial while reducing the
seven-valent relator to a conjugate of `h` or `h^(-1)`.  The exact screen has
`9*90,720=816,480` layouts and no hits.
