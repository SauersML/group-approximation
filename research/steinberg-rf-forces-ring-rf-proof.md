---
rg: 2
id: steinberg-rf-forces-ring-rf-proof
kind: route
title: The commutator relation spreads and multiplies the kernel of x_12 in a finite quotient, making it an ideal
target: steinberg-rf-forces-ring-rf
requires: []
---

Direct proof from the Steinberg relations.
- `x_ij(r) x_ij(s) = x_ij(r+s)`.
- `[x_ij(r), x_jk(s)] = x_ik(rs)` for distinct `i, j, k`.
- `[x_ij(r), x_kl(s)] = 1` for `j != k`, `i != l`.

**Spreading identities.** For distinct `i, j, k` the commutator relation gives
`x_ik(r) = [x_ij(r), x_jk(1)] = [x_ij(1), x_jk(r)]`. With `N >= 3`, starting from
`x_12(r)`:
- `x_1k(r) = [x_12(r), x_2k(1)]` for `k >= 3`;
- `x_i2(r) = [x_i1(1), x_12(r)]` for `i >= 3`;
- `x_ik(r) = [x_i1(1), x_1k(r)]` for `i != 1`, `k >= 3`, `i != k`;
- `x_i1(r) = [x_ik(r), x_k1(1)]` for `i != 1` and any `k` outside `{1, i}`.
So the normal closure of `x_12(r)` contains every `x_ij(r)`, `i != j`.

**1 and 2.** `r -> ρ(x_12(r))` is a homomorphism `(R,+) -> Φ`, so `I` is an additive
subgroup of finite index. If `r in I` then `ρ(x_ij(r)) = 1` for all `i != j`, by the spreading
identities. For `s in R`, `x_12(rs) = [x_13(r), x_32(s)]` and
`x_12(sr) = [x_13(s), x_32(r)]` both map to 1, so `rs, sr in I`.

**3.** `St_N(R/I)` is presented by the generators `x_ij(r̄)` and the Steinberg
relations over `R/I`. Equivalently, it is `St_N(R)` modulo the relators
`x_ij(a)`, `a in I`, since `x_ij(r) x_ij(r')^(-1) = x_ij(r - r')`. By 2, `ρ` kills
these relators.

**Consequence.** Suppose `0 != r` lies in every two-sided ideal of finite index. By
1–3, every finite quotient of `St_N(R)` factors through some `St_N(R/I)` in which
`x_12(r)` is trivial. Yet `x_12(r)` maps to the nontrivial elementary matrix
`e_12(r)`. ∎
