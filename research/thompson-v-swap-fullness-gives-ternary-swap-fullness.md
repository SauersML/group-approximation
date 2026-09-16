---
rg: 2
id: thompson-v-swap-fullness-gives-ternary-swap-fullness
kind: route
title: Push a Thompson-V swap corner solution into the ternary unit group algebra through the prefix-replacement embedding
target: ternary-leavitt-swap-idempotent-is-full
requires:
  - thompson-v-ternary-swap-idempotent-is-full
  - leavitt-algebras-l-k-1-n-are-simple
artifacts:
  - research/artifacts/anti-central-swap-fullness-gives-projective-2026-09-16.md
---

## Why sufficient

Proposition 7.1 and Corollary 7.2 of the 2026-09-16 artifact.

1. **Representation.** Let `R = L_(F_3)(1,2)` act on `F_3^(Omega)`, `Omega = {0,1}^N`, by `s_i e_xi = e_(i xi)`
   and `t_i e_(j xi) = delta_ij e_xi`. The Leavitt relations hold on basis vectors, so this is a nonzero unital
   representation `pi`. It is injective because `R` is simple (`leavitt-algebras-l-k-1-n-are-simple`).
2. **The embedding.** For `g in V` with complete prefix codes `(a_1..a_n) -> (b_1..b_n)`, put
   `u_g = sum_i s_(b_i) t_(a_i)`. Then `pi(u_g) e_xi = e_(g(xi))`.
   - `pi(u_g)` is the permutation operator of `g`, so by injectivity `u_g` depends only on `g`.
   - `u_(g g') = u_g u_(g')` and `u_1 = 1`.
   - Hence `g -> u_g` is an injective group homomorphism `V -> L_(F_3)(1,2)^x`.
3. **The swap.** The first-letter swap, with codes `(0,1) -> (1,0)`, goes to `s1 t0 + s0 t1 = w`.
4. **Pushing the equation.** The induced unital ring homomorphism `F_3[V] -> F_3[G]` sends
   `e_V = 2(1 + [w_V])` to `e = 2(1 + [w])`. It therefore sends a solution `c e_V b = 1` to a solution of
   `c' e b' = 1`.

This records the implication anticipated by the `distinct_from` entry of
`thompson-v-ternary-swap-idempotent-is-full`: witnesses inside `F_3[V]` are stronger than witnesses in the
unit-group algebra. The route puts that claim on a path to `ternary-leavitt-unit-group-nonsurjunctive`.
