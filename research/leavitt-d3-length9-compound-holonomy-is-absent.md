---
rg: 2
id: leavitt-d3-length9-compound-holonomy-is-absent
kind: claim
title: The first two-unary topology has incompatible coefficient-copy endpoints
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
`(1,1,7)`, if all nine coefficient slots are nonidentity, the two unary
coefficient corners have different reduced copy-index sequences.  Hence they
cannot become equal after either is used to solve for `z=t^3`, independently
of which nonidentity compound coefficient words occupy the slots.

In particular, every placement of the full-generating compound packet

```text
(u,u,v,v,r,e,p,a,c),
```

fails before the seven-valent target relator is consulted.  The faithful
exact screen has `9*90,720=816,480` layouts and independently confirms no
hits.  Thus any length-nine realization must contain an identity coefficient
slot, and after free simplification belongs to a shorter effective word class.
