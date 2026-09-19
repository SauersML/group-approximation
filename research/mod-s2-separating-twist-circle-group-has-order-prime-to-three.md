---
rg: 2
id: mod-s2-separating-twist-circle-group-has-order-prime-to-three
kind: claim
title: If the circle part of the separating-twist trace set of Mod(S_2) is finite then its order is prime to three
distinct_from:
  mod-s2-exact-representations-have-a-torelli-scalar-gap: that asserts omega is not in G_2 outright; this asserts it only on the finite branch, so it is strictly weaker and says nothing if G_2 = S^1.
  deligne-finite-parameter-group-has-period-prime-to-three: that is the same arithmetic split for the operator-norm parameter group P_op of Sp_4(Z); this is for the HS trace set of honest Mod(S_2) representations at one element.
  mod-s2-separating-twist-characters-are-nontangent-at-one: that is the analytic half excluding G_2 = S^1; this is the arithmetic half.
---

**OPEN.** In the notation of `mod-s2-separating-twist-character-semigroup-dichotomy`:

```text
if G_2 = mu_m, then 3 does not divide m.
```

Equivalently, `omega in X` implies `G_2 = S^1`.

**Why it matters.** Together with `mod-s2-separating-twist-characters-are-nontangent-at-one`, it gives
`mod-s2-exact-representations-have-a-torelli-scalar-gap`, through `mod-s2-torelli-scalar-gap-via-nontangency`.

**How it can fail.** Honest representations `rho_n` whose `rho_n(t_s)` are HS-close to `omega I` while the
cone condition holds at `1`. (ST5) of `deligne-torelli-character-counts-separating-twists` forbids exact
equality in each fixed dimension, but gives nothing uniform.

## Attempts
- **2026-09-18, swarm-0917-w12-w12-deligne-pull (probability-random): posed.** No test run.
  - Linear characters give `mu_5` (remark in the dichotomy node).
  - No construction of a point of `G_2` of order divisible by `2` or `3` is known here.
