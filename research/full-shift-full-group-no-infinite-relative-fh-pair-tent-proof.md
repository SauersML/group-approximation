---
rg: 2
id: full-shift-full-group-no-infinite-relative-fh-pair-tent-proof
kind: route
title: "Tent vectors: a tent on a sigma-orbit, or on the diagonal orbit of a pair split at one far site, is almost invariant under each fixed element but is knocked off by the far-reading or far-moving element, and a weighted sum gives the cnd function"
target: full-shift-full-group-has-no-infinite-relative-fh-subsets
requires: []
---

Notation is as in `full-shift-full-group-has-no-infinite-relative-fh-subsets`.

For a unitary representation `π` and a vector `f`, write `ψ_f(g) = ‖π(g)f − f‖²`. This is cnd,
with `ψ_f(e) = 0`.

For `R ≥ 1`, let `φ_R(c) = max(0, 1 − |c|/R)` for `c ∈ Z`. It is supported on `|c| < R`, has
`φ_R(0) = 1`, and is `1/R`-Lipschitz.

`K_g = ‖k_g‖_∞`. Note that `k_{g⁻¹}(gx) = −k_g(x)`, so `K_{g⁻¹} = K_g`.

## Step 0 (the orbit permutation)

Let `x` be aperiodic. Then `c ↦ σ^c x` is injective. Every `g ∈ [[X]]` maps the orbit of `x` to
itself, via `g σ^c x = σ^{τ(c)} x` with `τ(c) = c + k_g(σ^c x)`. Since `g` is a bijection of `X`
and `x` is aperiodic, `τ` is a bijection of `Z` with `|τ(c) − c| ≤ K_g`.

## Step 1 (the sliding estimate)

Let `τ` be a bijection of `Z` with `|τ(c) − c| ≤ K`. Then

`Σ_c |φ_R(τ⁻¹c) − φ_R(c)|² ≤ (2R + 2K − 1) K²/R²`.

*Proof.*
- Each term is at most `(K/R)²`, by the Lipschitz bound and `|τ⁻¹c − c| ≤ K`.
- A term is nonzero only if `|c| < R` or `|τ⁻¹c| < R`. Either way `|c| < R + K`, which leaves at
  most `2R + 2K − 1` values of `c`. ∎

## Step 2 (case (b): bounded windows, unbounded displacement)

Let `y ∈ [[X]]` with `K_y = D ≥ 2`.
- Choose a pattern at which `|k_y| = D`, and extend it to an aperiodic `x` with `|k_y(x)| = D`.
- Put `R = ⌊D/2⌋` and `f = Σ_c φ_R(c) δ_{σ^c x} ∈ ℓ²(X)`, with the permutation representation.

By Step 0, `π(g)f = Σ_c φ_R(c) δ_{σ^{τ_g(c)}x}`, so `ψ_f(g) = Σ_c |φ_R(τ_g⁻¹c) − φ_R(c)|²`.
- **Lower bound.** For `y`, `τ_y(0) = ±D` and `|±D| ≥ R`, so `φ_R(±D) = 0`. Hence
  `ψ_f(y) ≥ |φ_R(0) − φ_R(±D)|² = 1`.
- **Upper bound.** For every `g`, Step 1 gives `ψ_f(g) ≤ (2R + 2K_g − 1)K_g²/R²`.

## Step 3 (case (a): unbounded windows)

Let `y ∈ [[X]]` with window `w = w(y) ≥ 4`.

**The split pair.** By minimality of `w`, `k_y` does not depend only on `x_{[−w+1, w−1]}`. So there
are `u, u'` that agree on `[−w+1, w−1]` and have `k_y(u) ≠ k_y(u')`.
- Since `k_y` depends only on `[−w, w]`, only the sites `±w` matter.
- Changing those two sites one at a time from `u` to `u'`, some single change alters `k_y`.
- Hence there are `x, x'` that agree off one site `d ∈ {−w, w}` and have `k_y(x) ≠ k_y(x')`.
- Coordinates outside `[−w, w]` are free. Give `x` and `x'` the same aperiodic right tail, so that
  both are aperiodic.

**The vector.** Put `R = ⌊w/2⌋`, `p_c = (σ^c x, σ^c x')` and `f = Σ_c φ_R(c) δ_{p_c} ∈ ℓ²(X × X)`,
with the diagonal permutation representation. The `p_c` are distinct because `x` is aperiodic.

**Lower bound.**
- `π(y) δ_{p_0} = δ_q` with `q = (σ^k x, σ^{k'} x')`, where `k = k_y(x) ≠ k' = k_y(x')`.
- If `q = p_c`, then `c = k` because `x` is aperiodic, and `c = k'` because `x'` is aperiodic.
  That is a contradiction. So `q ∉ supp f`.
- Hence `(π(y)f − f)(q) = f(p_0) − 0 = 1`, and `ψ_f(y) ≥ 1`.

**Upper bound for fixed `g` with `w(g) ≤ w − R − 1`.**
- For `|c| < R`, the points `σ^c x` and `σ^c x'` differ only at site `d − c`, and
  `|d − c| ≥ w − R + 1 > w(g)`. So `k_g(σ^c x) = k_g(σ^c x') = τ_g(c) − c`, and
  `π(g) δ_{p_c} = δ_{p_{τ_g(c)}}`, where `τ_g` is the orbit permutation of Step 0 for `x`.
- Therefore `π(g)f = Σ_c φ_R(c) δ_{p_{τ_g(c)}}`, and by Step 1
  `ψ_f(g) = Σ_c |φ_R(τ_g⁻¹c) − φ_R(c)|² ≤ (2R + 2K_g − 1)K_g²/R²`.
- The hypothesis holds as soon as `w(g) < w/2 − 1`.

## Step 4 (gluing)

Let `Y ⊆ [[X]]` be infinite.
- For each `W, K`, only finitely many `g` have `w(g) ≤ W` and `K_g ≤ K`: `k_g` is then one of
  finitely many functions of `x_{[−W, W]}`.
- So `Y` contains a sequence `y_j` with either `w(y_j) → ∞` (case (a)) or `K_{y_j} → ∞` (case (b)).
- Pass to a subsequence with `R_j ≥ 4^j`, where `R_j = ⌊w(y_j)/2⌋` or `R_j = ⌊K_{y_j}/2⌋`. Let `f_j` be
  the vector of Step 3 or Step 2, and put `ψ = Σ_j j ψ_{f_j}`.

**`ψ` is finite and cnd.** Fix `g`.
- For all large `j`, the bound of Step 2 or 3 applies. In case (a) this uses
  `w(g) < w(y_j)/2 − 1`. It gives `j ψ_{f_j}(g) ≤ j(2R_j + 2K_g)K_g²/R_j² ≤ 3jK_g² 4^{−j}` once
  `R_j ≥ 2K_g`.
- The finitely many remaining terms are finite, since the `f_j` are finitely supported.
- So `ψ(g) < ∞`, and `ψ` is cnd as a pointwise limit of nonnegative combinations of cnd functions.

**`ψ` is unbounded on `Y`.** `ψ(y_j) ≥ j ψ_{f_j}(y_j) ≥ j`. ∎

## Corollaries

Restriction of a cnd function on `[[X]]` to `Γ ≤ [[X]]` is cnd on `Γ`, so every infinite
`Y ⊆ Γ` fails relative FH in `Γ`.

If `(Γ, H)` has relative (T), then `H` has relative FH in `Γ`. This is the easy direction of the
relative Delorme–Guichardet theorem: an affine isometric action whose linear part has almost
invariant vectors in the `H`-relative sense has an `H`-fixed point. So `H` is finite.

**Worked checks.**
- For `g_m = s_{E_m}`: take `x ∈ E_m` aperiodic and flip site `m` to get `x'`. Then `k(x) = 1`.
  Also `x' ∉ E_m`, and `x' ∉ σE_m` for `m` large because `z` is aperiodic, so `k(x') = 0`.
  The split site is at distance `m ≍ w(g_m)`.
- For `r_i = s_{R_i}` in `H_run`: take `x ∈ R_i` and flip site `i + 1`. The split is at distance
  `i + 1`, and `w(r_i) = i + 2`. Here `x' ∉ σR_i`, because `x'_{−1} = 1`.
- The script `experiments/pair-tent-2026-09-17/check_pair_tent.py` checks both bounds numerically.
