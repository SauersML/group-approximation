---
rg: 2
id: finite-dimensional-chart-reps-kill-one-transvection-lift-proof
kind: route
title: Compress h on V ⊗ V ⊗ V* and find a block of the odd part that its image misses
target: finite-dimensional-chart-reps-kill-one-transvection-lift
requires: []
artifacts:
  - research/artifacts/ternary-one-transvection-two-piece-lift-2026-09-12.md
---

## Why sufficient

Artifact Section 8.

1. **A ring map.** `rho = psi0 ⊗ psi0 ⊗ psi0*`, with `psi0*(x) = psi0(x^(-1))^T`, is a homomorphism
   `H -> GL(V ⊗ V ⊗ V*)` with `rho(z) = -1`. Its linear extension is a unital ring map on `eps_- F_3[H]`.
2. **The odd projection.** Split `V = V+ ⊕ V-` by `psi0(d1)`. Then `rho(d1)` acts on `V_a ⊗ V_b ⊗ V_c*` by
   the sign `abc`, so `rho(P1) = 2(1 - rho(d1))` projects onto the four odd blocks.
3. **A left inverse compresses.** If `v P1[h]P1 = P1` with `v = P1 v P1`, then `rho_O(v) rho_O(h) = 1` on the
   odd part `O`. So `rho_O(h)` is injective, hence onto, since `O` is finite-dimensional.
4. **A missing block.** Put `g = psi0(h)`.
   - `g V+ = V-` kills the `V+ -> V+` block of `g`.
   - `g^(-1) V- = V+` kills the `V-* -> V-*` block of `psi0*(h)`.
   - The component from an odd block `(abc)` into `V+ ⊗ V+ ⊗ V-*` vanishes. If `a = +` or `b = +`, the first
     block kills it; otherwise `a = b = -` forces `c = -`, and the second kills it.
   - `V+ ⊗ V+ ⊗ V-* != 0`, as `dim V+ = dim V- >= 1`. So `rho_O(h)` is not onto.

**Instances.** For a chart subalgebra `A ∋ s0` with a unital map `phi : A -> M_n(K)`, take `psi0 = GL_2(phi)`,
so that `psi0(h) = [[0,I],[-I,phi(s0)]]`. In the chart of a complete prefix code, `t_(0u) h s_(0w) = 0` and
`t_(1u) h^(-1) s_(1w) = 0` give the same block shape. For `F_3<s0,t0,t1>`, the Leavitt normal form shows
that `s0, t0 -> 1`, `t1 -> 0` is well defined.
