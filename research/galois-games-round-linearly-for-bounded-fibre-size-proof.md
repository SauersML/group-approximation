---
rg: 2
id: galois-games-round-linearly-for-bounded-fibre-size-proof
kind: route
title: Halving chain of K-cores of conjugated primitive kernels gives a permutable subgroup; the minimum with the free bound finishes
target: galois-games-round-linearly-for-bounded-fibre-size
requires: [primitive-projective-representations-have-a-trace-gap, galois-games-round-through-free-subgroups, galois-unique-game-value-is-transversal-expansion, free-rounding-pays-the-number-of-fibre-conjugates]
artifacts:
  - research/artifacts/ugc-rounding-normal-fibres-2026-09-13.md
  - research/artifacts/ugc-rounding-normal-fibres-part2-2026-09-13.md
---

Derivation (complete). Notation of the artifacts.

1. **Good components.** The symmetric SDP formula of
   `galois-unique-game-value-is-transversal-expansion` gives an admissible `phi`.
   Step (ii) of irreducible-kernel rounding in
   `galois-games-round-through-free-subgroups` uses only `phi = 0` on `K \ {e}`, so
   for any `K` it gives `K cap (intersection over good rho of ker rho) = {e}`,
   where good means `w_rho > 0` and `lambda_rho >= 1 - 3 eps`.
2. **Primitive kernels.** Write each good `rho = Ind_H sigma` with `sigma`
   primitive. By (16.2) of part 4, which uses the required trace gap, every
   conjugate of `ker sigma` has `mu`-mass at least `1 - 3 eps/c(G,m)`.
   `ker rho` is the intersection of these conjugates.
3. **`K`-cores.** Put `N_0 = K`. While `N_(i-1) != {e}`, pick `a in N_(i-1) \ {e}`,
   a good `rho` with `a notin ker rho`, and a conjugate `L_i` of `ker sigma_rho`
   omitting `a`. Put `L_i' = intersection over b in K of b L_i b^-1`. `K` permutes
   these conjugates, so `L_i'` is normalized by `K`. It omits `a`, and by
   conjugation invariance and a union bound over the at most `k` distinct
   conjugates, `mu(G \ L_i') <= 3 eps k/c(G,m)`. Put `N_i = N_(i-1) cap L_i'`,
   a proper subgroup, so there are at most `log_q k` steps.
4. **Permutable rounding.** `L = L_1' cap ... cap L_t'` is normalized by `K`, so
   `KL` is a subgroup. Also `L cap K = N_t = {e}` and
   `mu(G \ L) <= 3 eps k log_q k/c(G,m)`. Part 5 of
   `galois-games-round-through-free-subgroups` gives `val >= mu(L)`.
5. **Minimum.** The required free bound gives an `H` free on `G/K` with
   `mu(G \ H) <= 3 eps [G : N_G(K)] log_q k/c(G,m)`. Free-subgroup rounding (part 2
   of `galois-games-round-through-free-subgroups`) turns it into a value bound.
   Take the better of the two.
