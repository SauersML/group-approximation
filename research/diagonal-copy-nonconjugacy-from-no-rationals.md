---
rg: 2
id: diagonal-copy-nonconjugacy-from-no-rationals
kind: route
title: If (Q,+) is not in the Leavitt unit group, no infinite-order unit is conjugate to its diagonal copy
target: leavitt-units-are-not-conjugate-to-diagonal-copies
requires: [rationals-do-not-embed-in-binary-leavitt-unit-group, tbar-embeds-in-laurent-leavitt-unit-group]
---

Suppose `y` has infinite order and `y = w φ(y) w^(-1)`.
1. By the relative commutant formula (`no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`, Attempts,
   step 3), `y` commutes with `ρ_w(R)`.
2. `r ⊗ t^k -> ρ_w(r) y^k` is a unital homomorphism `L ⊗ F_2[t^±1] -> R`. It is injective, because `L` is central
   simple and `y` is transcendental over `F_2` (it has infinite order).
3. By `tbar-embeds-in-laurent-leavitt-unit-group` it carries `(Q,+) <= T̄` injectively into `L_(F_2)(1,2)^x`. This
   contradicts `rationals-do-not-embed-in-binary-leavitt-unit-group`. ∎

With `tensor-square-nonembedding-from-no-diagonal-conjugacy`, a proof that `(Q,+)` is not in `L_(F_2)(1,2)^x`
therefore answers Ara--Cortiñas Question 5.7 negatively over `F_2`.
