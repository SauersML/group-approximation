---
rg: 2
id: global-covariance-compression-proof
kind: route
title: Expand compressed covariance and isolate the uncontrolled source commutator
target: global-covariance-misses-capacity-compression
requires: []
---

If `vav^*=Z` approximately and `Q` is the leakage source, then exactly

```text
avQ-vQZ=(av-vZ)Q+v(ZQ-QZ).
```

The global word relator pays only the first term.  The second is the unknown
leakage commutator.  Taking `v=I`, `a=Z`, and any projection `Q` not reducing
`Z` gives zero global-relator error and positive compressed error, so no
estimate can omit it.

Making `v` normalize a finite packet preserves only a larger primitive
corner and still does not make `Q` reducing.  Moreover, global covariance
does not switch off when `Q=0`: it requires the entire HALT context
representation to extend to the chosen finite packet.  Countable
amplification cannot create absent packet weights.  By contrast the mixed
compressed row is vacuous when `Q=0`.  This proves both the soundness failure
and the completeness distinction.
