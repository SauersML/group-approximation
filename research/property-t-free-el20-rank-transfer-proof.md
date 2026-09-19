---
rg: 2
id: property-t-free-el20-rank-transfer-proof
kind: route
title: Apply the explicit binary-prefix elementary-group equivalence
target: property-t-free-el20-collapse-transfers-to-el12
requires: []
---

`LeavittFamily.rankSuccEquiv` gives

```text
EL_(a+1)(R) ~= EL_(b+1)(R)
```

for positive `a,b`, by flattening the explicit complete-prefix-code ring
equivalences `M_n(R) ~= R`.  Set `a=19`, `b=11`.  The MF radical is invariant
under group equivalence by the internal actual-corona radical functoriality
theorem.  Applying that theorem in both directions proves `(ERT1)`.

