---
rg: 2
id: bernoulli-pattern-expansions-are-finite-proof
kind: route
title: A single-site change is a bounded block, gapped resolvents decay exponentially with no growth factor, and an integer mixed trace bounded by C e^(-alpha d) vanishes
target: bernoulli-pattern-expansions-are-finite
requires:
  - bernoulli-assembly-injective-beyond-the-host
artifacts:
  - research/artifacts/bc-bernoulli-rank-locality-2026-09-13.md
---

The complete argument is in `research/artifacts/bc-bernoulli-rank-locality-2026-09-13.md`. The notation and Lemmas
R1, R2, R5, R7 and R8 come from `bernoulli-assembly-injective-beyond-the-host`.

1. **Approximation.** Take a self-adjoint configuration-local `a` with `||a - p|| < 1/8`, group support `E ∋ e` and
   coefficient window `W`.
   - At every finite-support `x`, `spec π_x(a) ⊆ [-1/8, 1/8] ∪ [7/8, 9/8]`.
   - `P_x = χ_([1/2, ∞))(π_x(a))` has rank `r_x(p)`.
2. **Blocks (Lemma L1).** Changing the symbol at `v` changes `π_x(a)` by a block `Δ_v` supported on
   `N(v) = v W^(-1) E`, of rank at most `m|W|`. For `d(u, v) > 2 max ℓ(W)`, the change at `v` is the same operator
   whether or not `u` has been changed.
3. **Decay (Lemma L2).**
   - Conjugate by `e^(αψ)` with `ψ` a truncated distance function.
   - The error is at most `Σ_g ||f_g|| (e^(α max ℓ(E)) - 1)`, a finite sum over `E`.
   - So `||1_A R_x(z) 1_B|| <= 2ρ e^(-α d(A, B))` on the contour `|z - 1| = 1/2`, and similarly for products of two
     resolvents. No growth bound on `G` is used.
4. **Mixed trace.** By the resolvent identity, `r_(x^(uv)) - r_(x^u) - r_(x^v) + r_x` equals
   `(1/2πi) ∮ Tr(R_11 Δ_u R_10 Δ_v R_01 + R_10 Δ_v R_01 Δ_u R_00) dz`. By cyclicity and L2 its absolute value is at most
   `C_0 e^(-α (d(u,v) - 2 max ℓ(N_0)))`. It is an integer, so it is `0` once `d(u, v) >= d_0`.
5. **Expansion.** RF Lemma R5 writes `n_([x])(y)` as the iterated difference over the support. A factor `∂_u ∂_v` at
   far sites vanishes identically, so `n(y)` has bounded diameter and finitely many orbits.
6. **Shapes and gaps.**
   - With `n(y)` finitely supported, the proof of RF Corollary R8 leaves only shapes (b) and (c).
   - A uniform gap passes to the algebra: the family of orbit representations is faithful, and their norms are
     lower semicontinuous in `x`.
   - So the spectral projection lies in `M_m(I_1 ⋊_r G)`, and item 2 gives item 4.
