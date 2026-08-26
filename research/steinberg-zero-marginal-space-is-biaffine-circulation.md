---
rg: 2
id: steinberg-zero-marginal-space-is-biaffine-circulation
kind: claim
title: The zero-marginal Steinberg chord space is the circulation space of the biaffine incidence graph
artifacts:
  - research/steinberg-biaffine-circulation-proof.md
distinct_from:
  steinberg-zero-marginal-fox-recurrence-is-zero: this identifies the large ambient space on which the two Fox rows must still be shown injective; it does not prove that recurrence claim.
---

**ESTABLISHED.**  Let the point vertices be `(a,b)`, the line vertices be
`(c,d)`, and join `(a,b)` to `(c,d)` when `d=ac-b`.  Identify the edge with
the chord `(a,b,c)`.  Then

```text
P(a,b)=sum_(edges at (a,b)) f,
H(c,d)=sum_(edges at (c,d)) f.                        (SBCI1)
```

Up to changing the sign on one bipartition, `P=H=0` is exactly the kernel
of the oriented incidence boundary.  The biaffine incidence graph is
connected and has `p^3` edges and `2p^2` vertices, so

```text
dim ker(P,H)=p^3-2p^2+1.                              (SBCI2)
```

Thus the second marginal-split node asks whether the two Fox rows kill this
explicit circulation module, not whether the marginal constraints alone
leave any room.

DERIVATION
steinberg-biaffine-circulation-proof
