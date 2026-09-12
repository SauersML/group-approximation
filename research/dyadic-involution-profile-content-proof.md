---
rg: 2
id: dyadic-involution-profile-content-proof
kind: route
title: Count J_2 blocks through the weight decomposition of a strict polynomial bifunctor, then apply dyadic polynomial rigidity
target: dyadic-involution-profiles-kill-bounded-degree-content
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/level-group-polynomial-content-2026-09-12.md
---

Artifact Sections 1–4.
1. **Additivity.** On orthogonal invariant pieces, `rk(sigma(h) - 1)` is the sum over pieces of
   `rk(e_i)·rank(rho_i(h) - 1)/d_i`.
2. **Jordan types.** In characteristic two an involution splits a module into `J_2` and `J_1`
   blocks, and its displacement rank is the number of `J_2` blocks. Projective modules restrict
   freely, so they have displacement exactly `1/2`.
3. **Polynomial profiles.** Decompose `V_N` and `V_N*` into `r` blocks `J_2` and `N - 2r` blocks
   `J_1`. The torus weight decomposition of a strict polynomial bifunctor of degree at most `D`
   has at most `D` effective summands. Counting patterns gives a polynomial of degree at most `D`
   in `r`, and every term with a `J_2` block carries a binomial factor vanishing at `r = 0`.
4. **Rigidity.** If `Q` has degree at most `D`, `Q(0) = 0`, and `Q(2r) = Q(r)` at `D + 1`
   integers, then `Q = 0`. Each piece's contribution at `r = 1` is a nonnegative normalized rank,
   so every polynomial piece has trivial transvection action, hence trivial `SL_N(F_2)` action.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 39 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
