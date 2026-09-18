---
rg: 2
id: odometer-factor-witnesses-mix-coordinates-proof
kind: route
title: An odometer factor forbids periodic points of every power, and triangular elements always have periodic points
target: odometer-factor-witnesses-mix-coordinates
requires:
  - triangular-subgroups-of-nv-contain-no-heisenberg-or-sl3z
---

**Item 1.** If `T^r p = p` with `r >= 1`, then `π(p) = π(T^r p) = π(p) + r` in
`Z_m`. So `r = 0` in `Z_m`, which is false: `Z_m` is torsion-free and `r ≠ 0`.

**Item 2.** Item 1 of `triangular-subgroups-of-nv-contain-no-heisenberg-or-sl3z`
states that every element of `T_k` has a periodic point, for every `k >= 1`.
Periodic points are carried along by conjugation by any homeomorphism of
`C^k`. That includes elements `f ∈ kV` and the coordinate permutation `σ`, which
normalizes `kV` (a brick map conjugated by `σ` is a brick map on the permuted
bricks). So every element of `f σ T_k σ^-1 f^-1` has a periodic point. If `T^r`
were such an element, it would contradict item 1.

**Item 3.** For `k = 1`, the flag condition is empty, so `T_1 = V`, and item 2
excludes every element of `V`. `V^k <= T_k` is stated in the triangular node.

**Item 4.** Item 1 again: a fixed constant configuration is a periodic point. ∎
