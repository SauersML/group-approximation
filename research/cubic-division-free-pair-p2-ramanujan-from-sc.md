---
rg: 2
id: cubic-division-free-pair-p2-ramanujan-from-sc
kind: route
title: The projective-plane sector is a summand of the congruence representation, so strong convergence makes every free pair's P^2 Schreier graphs asymptotically Ramanujan
target: cubic-division-free-pair-p2-schreier-asymptotically-ramanujan
requires: [cubic-division-congruence-representations-converge-strongly, cubic-division-congruence-sc-descends-to-thin-subgroups]
---

Let `D` be an algebra for which `cubic-division-congruence-representations-converge-strongly`
holds.  Let `A, B in Gamma_D` generate a free group `H`, put `Z = A + A^-1 + B + B^-1`, and
let `p` not be in `P_H`.

1. **Summand.**  With `G = SL_3(F_p)` and `x_0 = [e_1] in P^2(F_p)`, the map
   `f -> (g -> f(g x_0))` is a `G`-equivariant isometry, up to the factor `|Stab(x_0)|^(1/2)`,
   from `l^2(P^2(F_p))` into `l^2(G)`.  It sends constants to constants and mean-zero functions
   to mean-zero functions.  So `rho_p = l^2_0(P^2(F_p))` is a subrepresentation of
   `pi_p = l^2_0(G)`, and `||rho_p(Z)|| <= ||pi_p(Z)||`.
2. **Upper bound.**  By the hypothesis, `||pi_p(Z)|| -> ||lambda_(Gamma_D)(Z)||`.  By
   `cubic-division-congruence-sc-descends-to-thin-subgroups` (proof, step 4) this equals
   `||lambda_H(Z)||`, which is `2 sqrt 3` by Kesten.  So `limsup ||rho_p(Z)|| <= 2 sqrt 3`.
3. **Lower bound.**  Fix `m`.  Among the `4^(2m)` words of length `2m` in `A^(+-1), B^(+-1)`,
   those trivial in `F_2` contribute `p^2 + p` each to `tr rho_p(Z^(2m))`.  Each nontrivial one
   contributes `#Fix - 1`.  Its reduced characteristic polynomial is irreducible, hence
   separable (`cubic-division-ihara-traces-count-roots-mod-p`, part 1).  So for `p` large it
   fixes at most 3 points and contributes between `-1` and `2`.  Hence
   `tr rho_p(Z^(2m)) / (p^2 + p) -> tau(Z^(2m))`, and
   `liminf ||rho_p(Z)|| >= tau(Z^(2m))^(1/(2m))`.  The right side tends to
   `||lambda_H(Z)|| = 2 sqrt 3` as `m -> infinity`.
