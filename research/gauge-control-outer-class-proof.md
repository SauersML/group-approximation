---
rg: 2
id: gauge-control-outer-class-proof
kind: route
title: Compute the relative controlled automorphism modulo inner automorphisms
target: gauge-doubled-controls-remain-outer-separated
requires: []
---

In the class-two group with commutator subgroup `<J>`, let `r=AB` be a
central involution independent of `J`.  The two controlled automorphisms
send `P_t` to `AP_t` and `BP_t` respectively while agreeing elsewhere.
Their quotient fixes every other generator and sends

```text
P_t -> rP_t.
```

Every inner automorphism in a class-two group with derived subgroup `<J>`
sends a generator only to itself or `J` times itself.  Since `r` is
independent of `J`, the relative automorphism is outer.  Hence the two
controls represent different classes in `Out(P)` and cannot share one
multiplicity implementer unless `r` collapses to `1` or `J`.
