---
rg: 2
id: quadratic-descent-loss-admissibility-proof
kind: route
title: Compare the two loss rates against a fixed threshold
target: quadratic-descent-loss-is-admissible-linear-is-not
requires: []
artifacts:
  - research/artifacts/dimension-descent-criterion-2026-09-07.md
---

## Proof

**Quadratic.**  Let `epsilon_0 < 1/C` and `delta(U) < epsilon_0`.  Then

```text
delta(V) <= C delta(U)^2 = (C delta(U)) delta(U) < (C epsilon_0) epsilon_0
          < epsilon_0,
```

so the threshold is preserved, and the same estimate iterated gives
`C delta_j <= (C delta_0)^(2^j) -> 0`.

**Constant factor.**  A descent from dimension `d` terminates after at most
`d-1` steps, so the accumulated loss is at most `K^(d-1)`, and the criterion
is satisfied only if `delta(U) < epsilon_0 K^(1-d)`.  The bound depends on
`d`.  In an MF approximation the pair `(d_n, delta_n)` has
`delta_n -> 0` with no relation between the two sequences, so
`delta_n < epsilon_0 K^(1-d_n)` need never hold.
