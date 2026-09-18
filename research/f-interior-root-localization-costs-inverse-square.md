---
rg: 2
id: f-interior-root-localization-costs-inverse-square
kind: claim
title: "Switch-walk test functions localized at any non-dyadic germ root of Thompson's F prove amenability exactly when their gap beats inverse square in the radius"
distinct_from:
  f-dyadic-endpoint-switch-walk-gaps-are-inverse-square: that roots the switch walk at dyadic points and compares dyadic roots with each other; this roots it at a non-dyadic point xi on the germ Schreier graph F/F^0_xi and transfers radius-R localized test functions to the dyadic root 1/2 at cost O(R^2).
  f-ea-endpoint-localization-certificates-stall: that kills endpoint-localization certificates at 8/225 and only remarks that interior Chabauty-limit roots are transient; this proves a quantitative transfer from every interior germ root to the dyadic action.
  thompson-f-point-orbits-are-transient: that concerns recurrence of point orbits; this concerns spectral gaps of the switch walk on configurations, a different quantity.
  f-dyadic-inverted-orbit-is-subballistic-on-rare-events: that is the open inverted-orbit hole at dyadic roots; this does not decide it, but it shows an interior-root proof must meet the same inverse-square threshold.
artifacts:
  - experiments/f-interior-root-transfer-2026-09-17/dyadic_depth_distance.py
  - experiments/f-interior-root-transfer-2026-09-17/dyadic_depth_distance.json
  - experiments/f-interior-root-transfer-2026-09-17/depth_reduction.py
  - experiments/f-interior-root-transfer-2026-09-17/depth_reduction.json
---

**ESTABLISHED (elementary, with a finite computer check).**

**Setting.**
- `F` acts on `[0,1]` with generators `x_0, x_1`. `D` is the set of dyadic points of `(0,1)`.
- Fix `ξ ∈ (0,1) \ D`. Let `F^0_ξ` be the group of elements that are the identity on a neighbourhood
  of `ξ`, and put `X_ξ = F/F^0_ξ` with root `o = F^0_ξ`. For irrational `ξ`, `F^0_ξ = F_ξ` and `X_ξ = F·ξ`.
  Every such `F^0_ξ` is a Chabauty limit of dyadic point stabilizers.
- `L_ξ = (Z/2)^(X_ξ) ⋊ F` acts on `P_f(X_ξ)`. Let `μ` be uniform on `{e, x_0^{±1}, x_1^{±1}}` and
  `ν_ξ = λ ∗ μ ∗ λ`, where `λ` is uniform on `{e, δ_o}`. Its Dirichlet form is
  `E_ξ(f) = ½ Σ_{(a,s,b)} (1/20) Σ_A |f(δ^a s δ^b·A) − f(A)|²`, exactly as in
  `f-dyadic-endpoint-switch-walk-gaps-are-inverse-square` with the root `y` replaced by `o`.
- `B_R(ξ) = {w·o : |w| ≤ R}` is the Schreier ball. The **localized gap** is
  `κ_ξ(R) = inf E_ξ(f)/‖f‖²` over `f ≠ 0` supported on configurations `A ⊆ B_R(ξ)`.
- `gap(y)` for `y ∈ D` is as in `f-dyadic-endpoint-switch-walk-gaps-are-inverse-square`.

**Theorem.** For every `ξ ∈ (0,1) \ D` and every integer `R ≥ 0`,

    gap(1/2) ≤ 20 (24R + 99)² · κ_ξ(R).

**Ingredients.**
1. **Prefix reading.** A word `g` of length `ℓ` and a string `p` with `|p| ≥ ℓ+2` determine a string `q`
   with `||q| − |p|| ≤ ℓ` such that `g(0.pw) = 0.qw` for every `w`. So `g` is affine on the cylinder `[p]`.
2. **Ball matching.** Let `p` be the first `2R+8` binary digits of `ξ` and `y = 0.p1`. There is a
   bijection `ψ : B_{R+2}(ξ) → B_{R+2}(y)` with `ψ(o) = y` and `ψ(s·v) = s·ψ(v)` for `|v| ≤ R+1`. Hence
   `gap(y) ≤ κ_ξ(R)`.
3. **Depth reduction.** Every dyadic of depth `k ≥ 2` moves to smaller depth under some word of length
   `≤ 3`, so `d(y, 1/2) ≤ 3(depth(y) − 1)`.
   - The finite check is `depth_reduction.json`. It also records why checking depth `≤ 6` suffices, by
     prefix reading.
   - `dyadic_depth_distance.json` shows that the exact maximum distance at depth `k ≤ 14` is `2k − 3`. So
     the transport cost really is linear in depth.
4. **Transport.** Lemma (3a) of `f-dyadic-endpoint-switch-walk-gaps-are-inverse-square-proof`, with
   `d ≤ 6R + 24`.

**Consequences.**
- **(a) Sufficient criterion.** Suppose `liminf_R R² κ_ξ(R) = 0` for a single non-dyadic `ξ`. Then
  `gap(1/2) = 0`, and `F` is amenable by Step 1 of the endpoint proof and
  `thompson-f-amenable-iff-dyadic-action-extensively-amenable`.
- **(b) Uniform lower bound.** Suppose `F` is not amenable. Then `gap(1/2) > 0`, and
  `κ_ξ(R) ≥ gap(1/2) / (20(24R+99)²)` for every non-dyadic `ξ` and every `R`. The constant does not depend
  on `ξ`.
- **(c) Converse.** If `F` is amenable, then `L_ξ` is amenable, and `κ_ξ(R)` decreases to `0` as `R → ∞`
  for every `ξ`.
- **(d) Normal form for interior roots.**
  - The endpoint normal form "show `liminf m² κ(m) = 0`" extends to every root `F^0_ξ`. These roots are
    exactly the Chabauty limits of dyadic point stabilizers at non-dyadic points.
  - Changing the root does not lower the threshold below inverse square in the localization radius.

**Where the qualitative transfer dies.** The tempting route runs: "`F ↷ X_ξ` is extensively amenable and
`F_{y_j} → F^0_ξ` in Chabauty, so `F ↷ D` is extensively amenable." It fails at **base-point transport**.
- Ball matching reaches a dyadic root `y` of depth `2R+9`.
- Moving the toggle from `y` back to a fixed root costs `Θ(R)` letters, which by (3a) is a factor `Θ(R²)`
  in the Dirichlet form.
- Qualitative extensive amenability of `X_ξ` gives `κ_ξ(R) → 0` with no rate. It does not give the
  subsequential rate `o(R^{−2})` that (a) needs.

**Scope.**
- Neither direction of `thompson-f-is-amenable` is decided.
- An amenability proof would still need `κ_ξ(R) = o(R^{−2})` along a subsequence at some interior root.
- A class kill of interior-root localization certificates would still need a lower bound `κ_ξ(R) ≥ c/R²`.
- The endpoint theorem's strip-type upper bound `κ(m) ≤ π²/(5m²)` has no interior analogue proved here.
- The argument is elementary, and no priority is claimed.

Proof route: `f-interior-root-localization-costs-inverse-square-proof`.
