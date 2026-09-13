---
rg: 2
id: thompson-f-two-transitive-stabilizers-are-piecewise-closed-proof
kind: route
title: Glue stabilizer elements one dyadic breakpoint at a time using the splitting property
target: thompson-f-two-transitive-stabilizers-are-piecewise-closed
requires:
  - thompson-f-two-transitive-actions-satisfy-grid-condition
---

By item 4 of `thompson-f-two-transitive-actions-satisfy-grid-condition`, for
every dyadic `x ∈ (0,1)`, `H ∩ F_x = (H ∩ F_x^-)(H ∩ F_x^+)`. So if `u ∈ H`
fixes a dyadic `x`, the element `u^+` equal to `u` on `[x,1]` and to the
identity on `[0,x]` lies in `H`. Use functional composition.

Put `k_1 = h_1 ∈ H`, which agrees with `g` on `[0,x_1]`. Suppose `k_i ∈ H`
agrees with `g` on `[0,x_i]`. Let `u = k_i^{-1} ∘ h_{i+1} ∈ H`. Since
`h_{i+1}(x_i) = g(x_i) = k_i(x_i)`, `u` fixes the dyadic point `x_i`, so
`u^+ ∈ H`. Put `k_{i+1} = k_i ∘ u^+ ∈ H`:

- for `t ∈ [0,x_i]`, `u^+(t) = t`, so `k_{i+1}(t) = k_i(t) = g(t)`;
- for `t ∈ [x_i,1]`, `k_{i+1}(t) = k_i(k_i^{-1}(h_{i+1}(t))) = h_{i+1}(t)`,
  which equals `g(t)` on `[x_i,x_{i+1}]`.

After `n` steps, `k_n = g ∈ H`.

For the local form, take a Lebesgue number of the cover of `[0,1]` by the
agreement neighborhoods, choose a dyadic subdivision finer than it, and apply
the above.
