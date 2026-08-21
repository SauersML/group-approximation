---
rg: 2
id: canonical-full-overlap-proof
kind: route
title: Faithfulness turns equality of overlap trace into projection containment
target: canonical-full-type-overlap-is-algebraic-corner-containment
requires: []
---

Put `p=uqu^*`.  Since `p,r` are projections,

```text
tau(q)-tau(q u^* r u q)=tau(p)-tau(prp)=tau(p(1-r)p).
```

The last element is positive.  Faithfulness of the canonical trace makes the
difference zero exactly when `p(1-r)p=0`.  This is equivalent to
`(1-r)p=0`, hence to `p<=r`.  Conversely `p<=r` gives `rp=p` and equality.
