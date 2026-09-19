---
rg: 2
id: codense-gap-exact-projective-proof
kind: route
title: Apply the co-dense Poincare inequality to the inner automorphism witness
target: codense-gap-controls-exact-projective-tuples
requires: []
---

An exact projective representation becomes the honest representation
`pi=Ad(rho)` on `M_d`.  Apply the assumed conjugation Poincare inequality
for `pi` to `X=Ad(U)`.  Co-density makes its invariant projection commute
with `pi(h)`, costing the factor four in `(CDG5)`.  Finally

```text
||[Ad(U),Ad(rho(g))]_add||_2^2
 =2(1-|tr_d([U,rho(g)])|^2),
```

so the ordinary displacement estimate is exactly the desired projective
trace-square estimate.
