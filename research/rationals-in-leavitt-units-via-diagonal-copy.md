---
rg: 2
id: rationals-in-leavitt-units-via-diagonal-copy
kind: route
title: An infinite-order unit in a relative commutant embeds L ⊗ F_2[t^±1], hence T-bar and (Q,+), in the Leavitt unit group
target: rationals-embed-in-binary-leavitt-unit-group
requires: [infinite-order-leavitt-unit-conjugate-to-its-diagonal-copy, tbar-embeds-in-laurent-leavitt-unit-group]
---

1. By `infinite-order-leavitt-unit-conjugate-to-its-diagonal-copy`, form (b), there is a unital embedding
   `θ : L_(F_2)(1,2) ⊗ F_2[t^±1] -> R = L_(F_2)(1,2)`. It restricts to an injective homomorphism of unit groups.
2. By `tbar-embeds-in-laurent-leavitt-unit-group`, `(Q,+) <= T̄ <= (L ⊗ F_2[t^±1])^x`.
3. So `θ ∘ Ψ` embeds `T̄`, and with it `(Q,+)`, in `U = R^x`. ∎

Explicitly, with `y = u φ(y) u^(-1)`, the dyadic rotation lifts `r_m` go to
`Σ_(j < 2^m − 1) ρ_u(s_(w_(j+1)) t_(w_j)) + ρ_u(s_(w_0)) y ρ_u(t_(w_(2^m − 1)))`, where
`ρ_u(s_i) = u s_i` and `ρ_u(t_i) = t_i u^(-1)`. These square to one another, and `r_0 = y`.
