---
rg: 2
id: steinberg-rf-forces-ring-rf-proof
kind: route
title: Weyl conjugation and the commutator relation make the kernel of x_12 in a finite quotient an ideal
target: steinberg-rf-forces-ring-rf
requires: []
---

Direct proof from the Steinberg relations.
- `x_ij(r) x_ij(s) = x_ij(r+s)`.
- `[x_ij(r), x_jk(s)] = x_ik(rs)` for distinct `i, j, k`.
- `[x_ij(r), x_kl(s)] = 1` for `j != k`, `i != l`.

**Weyl elements.** Put `w_ij = x_ij(1) x_ji(-1) x_ij(1)`. For distinct indices the
Steinberg relations give `w_ij x_kl(r) w_ij^(-1) = x_(π(k)π(l))(±r)`, with `π` the
transposition `(i j)`. This is standard, e.g. Milnor, *Introduction to Algebraic
K-theory*, §9. Conjugates of `x_12(r)` therefore include `x_ij(±r)` for all
`i != j`, because `N >= 3`.

**1 and 2.** `r -> ρ(x_12(r))` is a homomorphism `(R,+) -> Φ`, so `I` is an additive
subgroup of finite index. If `r in I` then `ρ(x_ij(r)) = 1` for all `i != j`, by Weyl
conjugation. For `s in R`, `x_12(rs) = [x_13(r), x_32(s)]` and
`x_12(sr) = [x_13(s), x_32(r)]` both map to 1, so `rs, sr in I`.

**3.** `St_N(R/I)` is presented by the generators `x_ij(r̄)` and the Steinberg
relations over `R/I`. Equivalently, it is `St_N(R)` modulo the relators
`x_ij(a)`, `a in I`, since `x_ij(r) x_ij(r')^(-1) = x_ij(r - r')`. By 2, `ρ` kills
these relators.

**Consequence.** Suppose `0 != r` lies in every two-sided ideal of finite index. By
1–3, every finite quotient of `St_N(R)` factors through some `St_N(R/I)` in which
`x_12(r)` is trivial. Yet `x_12(r)` maps to the nontrivial elementary matrix
`e_12(r)`. ∎
