---
rg: 2
id: leavitt-degree4-strict-omega-four-cycle-no-go
kind: claim
title: A strict degree-four Omega four-cycle has no cyclic realization through length twenty
artifacts:
  - research/artifacts/classify-degree4-strict-four-cycle.py
---

For degree four, among cyclic sign words of length at most twenty, the orbit
profile `(1,1,3,3)` occurs only at length eight.  Its 20 sign words form three
dihedral classes, represented by

```text
--++++++       -++-++++       -+++-+++
```

In the last two classes, which are exactly the classes having two singleton
corners in each trivalent orbit, the corrected signed pattern
`(+,-,+)` cannot realize the strict common-tail relations

```text
(H, H^-1, H Y S H^-1),    (H, H^-1, H Y T H^-1)
```

with either unary corner used as the pivot `H`, unless all carrier slots are
trivial.  Hence these classes cannot transport
`S=Omega(a,r)=1` to `T=Omega(c,p)!=1` by the literal four-cycle compiler.

This is only a no-go for the strict corrected corner pattern.  It does not
exclude a longer residual profile or a Leavitt-specific transport whose
intermediate corners do not equal `H` and `H^-1` separately.
