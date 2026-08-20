---
rg: 2
id: self-referential-bcs-doubling-tape-proof
kind: route
title: Specialize the Fanizza doubling identities to the fixed-point nonmembership index
target: self-referential-bcs-doubling-tape
requires:
  - self-referential-bcs-nonzero-signal-collapse
  - fanizza-bcs-polynomial-doubling-tape
---

In the proof of `self-referential-bcs-nonzero-signal-collapse`, the fixed-point
index `m_*` does not belong to the halting set `L`. Apply `(FDB1)--(FDB3)` at
this one index. The factors `m_*^k` and all quantitative embedding constants
are now fixed computable constants, so `(FDB2)` becomes

```text
C_* (n+1)^(k_*).
```

The fixed-point proof already gives `D!=0`. Therefore the same finite BCS has
both the algebraically nonzero base signal and the polynomial-cost infinite
doubling recurrence.
