---
rg: 2
id: stw82-odd-support-cycle-stable-two-colour-obstruction-proof
kind: route
title: Find a monochromatic edge in the odd support cycle
target: stw82-odd-support-cycle-stable-two-colour-obstruction
requires:
  - stw82-indivisible-order-zero-reuse-is-graph-colouring
---

Every assignment of the vertices of an odd cycle to two colours has a
monochromatic edge, say `v_i,v_(i+1)`.  Put

```text
h'_v=phi'_v(1).
```

Evaluation at the unit gives `norm(h_v-h'_v)<=delta`.  Since the two maps
on the monochromatic edge belong to one order-zero direct sum, the support
criterion gives

```text
h'_(v_i) h'_(v_(i+1))=0.
```

Therefore

```text
norm(h_(v_i) h_(v_(i+1)))
 <= norm((h_(v_i)-h'_(v_i)) h_(v_(i+1)))
    +norm(h'_(v_i)(h_(v_(i+1))-h'_(v_(i+1))))
 <= 2 delta.                                          (O3)
```

The left side is at least `kappa`, proving (O2).  The proof makes no use of
a fixed cycle or fixed colouring, so the sequential assertion follows
stage by stage.
