---
rg: 2
id: fpbs-mal-iid-chord-graphings-floor-union-route
kind: route
title: First-moment union bound over vertex-simple chains of relative positions, closed by a uniform exponential chain count
target: fpbs-mal-iid-chord-graphings-floor
requires: [fpbs-mal-simple-chain-count-uniform]
artifacts:
  - research/artifacts/fpbs-iid-chord-union-bound-2026-09-19.md
---

Artifact §1.

**1. Reduction.** `x` and `bx` are `E_K v Theta`-equivalent iff the classes
`K` and `Kb` are joined in the class graph. That happens iff they are
joined by a vertex-simple path `C_0..C_n`.

**2. Step events.** Take a step `C_{i-1} = Ky -> C_i = Kgy`. The points
`ky` of `C_{i-1}` reach `C_i` exactly with labels in `K g k^{-1}`. These sets
are pairwise disjoint by malnormality, and their union is `D_i`. The same
holds from the side of `C_i` with `D_i^{-1}`. The step's source events
therefore have total weight `epsilon q(D_i)`.

**3. Distinct sources.** In a vertex-simple path, a single point cannot be
the source of two steps: its one edge would have to land in `C_{i-1}` and
in `C_{i+1}`. Distinct points are independent, so each path contributes at
most `epsilon^n prod q(D_i)`.

**4. Sum.** Sum over paths, which gives the count `N_n`, and over `n`. With
`N_n <= rho^n` from `fpbs-mal-simple-chain-count-uniform`, and using
`sum_D q(D) <= 2`,

```text
P[x ~ bx] <= sum_n (2 epsilon rho)^n <= 1/2      for epsilon <= 1/(6 rho).
```

So `E_K v Theta ≠ E_F`, and `epsilon_0 = 1/(6 rho)`. ∎ (modulo the
requirement)
