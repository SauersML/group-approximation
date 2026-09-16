---
rg: 2
id: sol-lattice-dehn-action-bound-proof
kind: route
title: "Fiber distortion or an invariant area form forces the Dehn action bound for every action of a hyperbolic Sol lattice"
target: sol-lattice-actions-satisfy-the-dehn-action-bound
requires: []
artifacts:
  - research/artifacts/sol-lattice-dehn-action-bound-2026-09-16.md
---

Direct proof. The full argument, with all lemmas, is in
`research/artifacts/sol-lattice-dehn-action-bound-2026-09-16.md`. Write
`R(n) = δ_X(n) · max_v δ_{G_v}(dist_X‾(δ_X(n)))`, under normalization (N) of
the target claim.

1. **Exponential upper bound (artifact §2).** `δ_G(n) ≤ C^n`. Move each
   `t`-letter left through the fiber words, multiplying their length by at most
   `K` and paying `O(length)` relators each time. The `t`-exponent sum is `0`,
   so what remains is a fiber word of length `≤ nK^n` with area `≤ (nK^n)²` in
   `ℤ²`.
2. **Subgroups (§3).** If `H ∩ ℤ² ≠ 0`, then `H ≤ ℤ²` or `[G : H] < ∞`. For
   `w t^k ∈ H` with `k ≠ 0` and `0 ≠ y ∈ H ∩ ℤ²`, `M^k y` is independent of
   `y`, because `M^k` has irrational eigenvalues.
3. **Case 0: a vertex stabilizer of finite index.** `δ_{G_x} ≃ δ_G` by the
   classical quasi-isometry invariance of Dehn functions (Alonso 1990), and
   `R(n) ≥ δ_{G_x}(n)`.
4. **Case 1: a vertex stabilizer that is a nontrivial subgroup of `ℤ²`.**
   - `ℓ_G(z^m) = O(log |m|)` (§4). Expand `m ∈ ℤ[λ]` greedily as
     `Σ_{j ≤ K} c_j λ^j + Σ_{j ≤ K'} d_j λ^{−j} + s`, with bounded digits,
     `K, K' = O(log |m|)` and `s` in a finite set, using the lattice embedding
     `ℤ[λ] → ℝ²`, `p ↦ (p, p')`. Map it to `ℤ[M]` and realize it by Horner
     words in `t`.
   - `G_x` is free abelian, so `z` is undistorted in it. Hence
     `dist_X(n) ≽ e^n`, and `R(n) ≥ dist_X(n)` under (N).
5. **Case 2: all other actions.** Every vertex stabilizer meets `ℤ²` trivially,
   so it is trivial or `⟨w t^k⟩` with `k ≠ 0`.
   - `G` acts on `ℝ²` by `t·p = Mp` and translations by `ℤ²`. A nontrivial
     stabilizer has a unique fixed point, since `det(M^k − I) ≠ 0`. This gives
     an equivariant `f : X^(0) → ℝ²`.
   - **Area transfer (§5).** `A(x, y) = ½ det(f(x), f(y))` on oriented edges
     satisfies `|A(γ)| ≤ C_X · Vol(φ)` for every admissible filling `φ` of `γ`.
     An admissible map is cellular; nonsingular 2-cells push forward to `±σ`
     and singular ones to `0`. The triangle areas `|A(∂σ)|` are constant on
     orbits because `|det| = 1`.
   - **Orbit polygons (§6).** For an edge loop `γ_w` built from a word `w` of
     length `m`, `|A(γ_w) − sh(P_w)| ≤ C'm`, where `P_w` is the orbit polygon
     of a base point.
   - **Commutator polygon (§7).** For `w_n = [t^n a t^{−n}, t^{−n} a t^n]`,
     `sh(P_{w_n}) = det(M^n e_1, M^{−n} e_1)` for every base point. Its absolute
     value is `c(|λ|^{2n} − |λ|^{−2n})` with `c > 0`, since `e_1` is not an
     eigenvector.
   - So `δ_X(L(8n + 4)) ≥ c_1 |λ|^{2n} − O(n)`, i.e. `δ_X ≽ e^n`, and
     `R(n) ≥ δ_X(n)` under (N).
6. **Conclusion.** In every case `R ≽ δ_G`.

The exact identity of step 5 (commutator polygon) and `det(M^k − I) ≠ 0` are
also checked in exact rational arithmetic by
`experiments/zaremsky-1-17-dehn-function-from-cocompa-swarm-2026-09-16/sol_orbit_polygon_area.py`.
The proof does not depend on the script.

Definitions (`≼`, `dist^G_H`, admissible maps, `Vol`, `FVol`, `δ_X`) are those
of Llosa Isenrich–Weis, arXiv:2608.07191v1 (7 August 2026), §2.1,
Definitions 2.2–2.3, read on 2026-09-16.
