---
rg: 2
id: forbidden-packet-reynolds-holonomy-payment-proof
kind: route
title: Combine the predicate Reynolds rank gap with adjoint holonomy payment
target: forbidden-packet-reynolds-holonomy-payment
requires:
  - predicate-rank-jump-forces-adjoint-reynolds-gap
  - reynolds-rank-gap-forces-hs-holonomy-energy
---

The predicate theorem gives

```text
(rank(R_A)-rank(R_B))/d^2 >= (3/(4D_0^2K))q^2.
```

Apply `(RHG2)` to the transported Reynolds enumerations. It bounds the same
left side above by `2 epsilon`. Division by two is exactly `(FRH1)`.

