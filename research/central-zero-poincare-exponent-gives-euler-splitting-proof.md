---
rg: 2
id: central-zero-poincare-exponent-gives-euler-splitting-proof
kind: route
title: "Rescaled nonsingular Gaussian actions of the cnd function: zero central Poincare exponent makes z dissipative, a fundamental domain for <z> is the Q-space, and fibrewise l2 norms push the Gaussian half-densities down to almost invariant vectors"
target: central-zero-poincare-exponent-gives-euler-splitting
requires: []
---

Notation as in the target. Fix `ψ` with `δ_z(ψ) = 0`.

## Imports

- (I1) (Schoenberg–Delorme–Guichardet; [BHV08, Ch. 2]) A function `ψ` with `ψ(e) = 0` on a
  countable group is cnd iff there are an affine isometric action `α` on a real Hilbert space `H`
  and `x ∈ H` with `ψ(g) = ‖α(g)x − x‖²`. `H` can be taken to be the closed affine span of the
  orbit `α(G)x`, so it is separable.
- (I2) Arano–Isono–Marrakchi, *Ergodic theory of affine isometric actions on Hilbert spaces*,
  arXiv:1911.04272v4 (AIM). Verbatim:
  - Conventions: "All locally compact groups are assumed to be Polish (second countable). All
    Hilbert spaces are assumed to be separable. All measure spaces are standard borel spaces."
  - Introduction: "one can naturally associate to every real affine Hilbert space H a family of
    equivalent probability measures (µx)x∈H on some standard borel space Ĥ" … "for every affine
    isometry g ∈ Isom(H), there exists a unique (up to null-sets) measurable map ĝ : Ĥ → Ĥ such
    that ĝ∗µx = µgx for all x ∈ H. It follows that every affine isometric action α : G ↷ H of a
    locally compact group G induces a nonsingular Gaussian action α̂ : G ↷ Ĥ which preserves the
    measure class of (µx)x∈H."
  - "Proposition 4.6. … (iii) For all x,y ∈ H, ⟨µx^{1/2}, µy^{1/2}⟩ = exp(−(1/8)‖y − x‖²)."
  - "Proposition 4.9. Let H be an affine Hilbert space and let g ∈ Isom(H) with g ≠ id. Then
    ĝ ∈ Aut(Ĥ) is essentially free."
  - Introduction: "A free nonsingular action σ : G ↷ X of a locally compact group is called
    dissipative (or equivalently of type I) if and only if it is conjugate to a nonsingular action
    of the form G ↷ G⊗Y where G acts only on the first coordinate by left translation. … In
    particular, when G is discrete, this means that σ admits a fundamental domain."
  - Introduction: "The (quadratic) Poincaré exponent δ(α) ∈ [0, +∞] is defined as the infimum of
    all s > 0 such that ∫_G e^{−s‖gx−y‖²} dg < +∞, x,y ∈ H. This number does not depend on the
    choice of x,y ∈ H".
  - "Theorem B. Let α : G ↷ H be an affine isometric action of a locally compact group G. There
    exists t_diss(α) ∈ [0, +∞] such that the Gaussian action α̂_t is recurrent for all
    t < t_diss(α) and dissipative for all t > t_diss(α). Moreover, we have the following
    inequalities √(2δ(α)) ≤ t_diss(α) ≤ 2√(2δ(α))." Here `α̂_t` is the Gaussian action of the
    rescaled action `α_t : G ↷ H_t`, so `α̂_1 = α̂`.
- (I3) Standard measure theory: nonsingular maps pull back and push forward null sets; a
  countable union of null sets is null.

Reading of (iii): `µ_x^{1/2}` is the half-density of `µ_x`. For any `σ`-finite `ν` in the class,
it is the vector `(dµ_x/dν)^{1/2} ∈ L²(ν)`, and the inner product is the Hellinger affinity
`∫ (dµ_x/dν · dµ_y/dν)^{1/2} dν`, which does not depend on `ν`. (Check from Prop. 4.6(i)–(ii):
with `d = ‖y − x‖`, the affinity is `e^{−d²/4} ∫ e^{⟨ω−x, y−x⟩/2} dµ_x = e^{−d²/4} e^{d²/8}`.)

## Step 1 (the space Y)

For `j ≥ 1` put `ψ_j = ψ/j`. It is cnd, and `δ_z(ψ_j) = j δ_z(ψ) = 0`. By (I1) choose an affine
isometric action `α_j : G ↷ H_j` on a separable space and `x_j ∈ H_j` with
`ψ_j(g) = ‖α_j(g)x_j − x_j‖²`. By (I2) let `(Ĥ_j, (µ^j_x)_{x ∈ H_j})` be its Gaussian density and
`α̂_j` the nonsingular Gaussian action. Put

    Y = ⊔_j Ĥ_j,    ν = ⊔_j µ^j_{x_j}   (a standard σ-finite measure),

with `G` acting by `ĝ = ⊔_j α̂_j(g)`. This preserves the measure class of `ν`.

**Point realization.** By uniqueness in (I2), `α̂_j(g) ∘ α̂_j(h)` and `α̂_j(gh)` both push every
`µ^j_x` to `µ^j_{ghx}`, so they agree off a null set, and `α̂_j(e) = id` a.e. Let `N_0` be the
union of these countably many null sets. Let `Y_0` be the complement of the union of
`(ĝ_1 ∘ ⋯ ∘ ĝ_k)^{-1}(N_0)` over all finite words. It is conull by (I3), and invariant under every
`ĝ`. On it `g ↦ ĝ` is a genuine action by nonsingular Borel bijections. Replace `Y` by `Y_0`.

## Step 2 (z acts freely and dissipatively)

Restrict `α_j` to `⟨z⟩ ≅ Z`, a discrete group with counting Haar measure. Its Gaussian action is
the restriction of `α̂_j`, by uniqueness in (I2).

- **Poincaré exponent.** At `x = y = x_j`, the integral in (I2) is
  `Σ_m exp(−s ψ(z^m)/j)`, which is finite for all `s > 0` by (SL). Since it does not depend on
  `x, y`, `δ(α_j|_Z) = 0`.
- **Dissipative.** Theorem B gives `t_diss(α_j|_Z) ≤ 2√0 = 0 < 1`, so `α̂_j|_Z = (α̂_j)_1|_Z` is
  dissipative.
- **Free.** If `α_j(z^m) = id` for some `m ≠ 0`, then `ψ(z^{mk}) = 0` for all `k`, and
  `Σ_m exp(−sψ(z^m)) = ∞` for every `s`, which contradicts (SL). So by Prop. 4.9, each `ẑ^m`
  (`m ≠ 0`) is essentially free.

Discard the `G`-saturation of the union of the fixed-point sets of `ẑ^m`, `m ≠ 0`. Since `G` is countable,
the saturation is a countable union of images of a null set, so it is null by (I3). The `Z`-action is
now free. By the verbatim dissipativity statement (discrete
group), each `Ĥ_j` has a Borel fundamental domain `W_j` for `⟨z⟩`: the sets `z^m W_j` are pairwise
disjoint and their union is conull. Also discard the `G`-saturation of the null complement.

Call the remaining conull `G`-invariant set `Y_1`, and put `W = Y_1 ∩ ⊔_j W_j`. Every `y ∈ Y_1` is
uniquely `y = ẑ^{m(y)} π(y)` with `m(y) ∈ Z` and `π(y) ∈ W`. Both maps are Borel:
`m^{-1}(k) = ẑ^k W`, and `π = ẑ^{-k}` there.

## Step 3 (the Q-space and the integer cocycle)

For `g ∈ G` and `w ∈ W` put

    g·w = π(ĝ w) ∈ W,    β(g, w) = m(ĝ w) ∈ Z.

Both are Borel. Since `z` is central and `Y_1` carries a genuine action, `ĝ ẑ = ẑ ĝ` on `Y_1`. So
for `y = ẑ^m w`:

    ĝ y = ẑ^m ĝ w = ẑ^{m + β(g, w)} (g·w),   hence   π(ĝ y) = g·π(y).     (★)

- **Action and cocycle.** `ĝ ĥ w = ĝ ẑ^{β(h,w)} (h·w) = ẑ^{β(h,w) + β(g, h·w)} (g·(h·w))`. By
  uniqueness of the decomposition, `(gh)·w = g·(h·w)` and `β(gh, w) = β(g, h·w) + β(h, w)`, for
  every `w ∈ W`.
- **Centre.** `ẑ w ∈ ẑ W`, so `z·w = w` and `β(z, w) = 1` for every `w`. So `(gz)·w = g·w`, and the
  action factors through `Q`.
- **Measure.** Put `μ = ν|_W`, which is standard and σ-finite. On the Borel partition
  `W ∩ ĝ^{-1}(ẑ^k W)` (`k ∈ Z`), the map `w ↦ g·w` equals `ẑ^{-k} ĝ`, which is nonsingular. So
  each `q ∈ Q` acts nonsingularly, with inverse given by `q^{-1}`.

## Step 4 (fibrewise pushdown of half-densities)

For `k ∈ Z`, `ẑ^{-k}` maps `ẑ^k W` bijectively onto `W` and is nonsingular. Let
`ρ_k = d((ẑ^{-k})_*(ν|_{ẑ^kW}))/dμ`. Then for Borel `f ≥ 0` on `Y_1`,

    ∫_{Y_1} f dν = ∫_W Σ_k f(ẑ^k w) ρ_k(w) dμ(w).

For `ξ ∈ L²(Y_1, ν)` define the (nonlinear) pushdown

    (Pξ)(w) = ( Σ_k |ξ(ẑ^k w)|² ρ_k(w) )^{1/2} = ( dπ_*(|ξ|²ν)/dμ )^{1/2}(w).

Write `κ_Y`, `κ_W` for the Koopman representations, with the convention of the target.

- (a) `‖Pξ‖ = ‖ξ‖`, by the disintegration formula.
- (b) `‖Pξ − Pη‖ ≤ ‖ξ − η‖`. Indeed `‖ξ − η‖² ≥ ‖ξ‖² + ‖η‖² − 2∫|ξ||η| dν`, and
  `‖Pξ − Pη‖² = ‖ξ‖² + ‖η‖² − 2∫ Pξ·Pη dμ`. By the disintegration formula and Cauchy–Schwarz in
  `ℓ²(Z)` at each `w`, `∫|ξ||η| dν = ∫ Σ_k |ξ||η|(ẑ^k w) ρ_k(w) dμ ≤ ∫ Pξ·Pη dμ`.
- (c) `P(κ_Y(g)ξ) = κ_W(p(g)) Pξ`. For any nonsingular action and a finite measure `λ ≪` the base
  measure, one has `κ(g)(dλ/d·)^{1/2} = (d(g_*λ)/d·)^{1/2}`: substitute into
  `(κ(g)F)(y) = RN_g(y)^{1/2} F(g^{-1}y)` and use `RN_g = d(g_*ν)/dν`. So
  `|κ_Y(g)ξ|²ν = ĝ_*(|ξ|²ν)`. By (★), `π_* ĝ_* = (g·)_* π_*`. Apply the same identity on `W`.

## Step 5 (almost invariant vectors)

Let `ξ_j = 1_{Ĥ_j ∩ Y_1}`. Since `ν = µ^j_{x_j}` there, `ξ_j = (dµ^j_{x_j}/dν)^{1/2}` is a unit
vector. By Step 4(c) on `Y` and `ĝ_*µ^j_x = µ^j_{α_j(g)x}`, we get
`κ_Y(g)ξ_j = (dµ^j_{α_j(g)x_j}/dν)^{1/2}`. By Prop. 4.6(iii),

    ⟨κ_Y(g)ξ_j, ξ_j⟩ = exp(−‖α_j(g)x_j − x_j‖²/8) = exp(−ψ(g)/(8j)),

and `‖κ_Y(g)ξ_j − ξ_j‖² = 2 − 2 exp(−ψ(g)/(8j)) → 0` as `j → ∞`, for every `g`. Let `F_j = Pξ_j`.
By (a) it is a unit vector in `L²(W, μ)`. By (c) and (b), for `q = p(g)`,

    ‖κ_W(q)F_j − F_j‖ = ‖P(κ_Y(g)ξ_j) − Pξ_j‖ ≤ ‖κ_Y(g)ξ_j − ξ_j‖ → 0.

So `(W, μ)`, the `Q`-action and `β` satisfy the Theorem. ∎

## Remarks

- Only the upper bound `t_diss ≤ 2√(2δ)` of Theorem B is used. With it, (SL*) of the target is
  enough directly: use `ψ_j` with `δ_z(ψ_j) < 1/8`, so `2√(2δ) < 1`.
- The pieces are needed because a single Gaussian action has `⟨κ(g)µ^{1/2}, µ^{1/2}⟩ = e^{−ψ(g)/8}`,
  which is fixed. Almost invariance comes from scaling `ψ` down, and (SL) is exactly what keeps
  `z` dissipative at every scale.
