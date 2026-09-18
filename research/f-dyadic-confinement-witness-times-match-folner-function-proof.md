---
rg: 2
id: f-dyadic-confinement-witness-times-match-folner-function-proof
kind: route
title: Extract an almost invariant lamp law from the switch-walk-switch chain and push it to a Følner set of F; conversely, lift a Følner set of F to a lamplighter Følner set and use the spectral lower bound
target: f-dyadic-confinement-witness-times-match-folner-function
requires:
  - thompson-f-amenable-iff-dyadic-action-extensively-amenable
  - thompson-f-folner-function-exceeds-every-tower
---

Notation as in the target.
- `Z = (Z/2)^{(D)}`, identified with the finite subsets of `D`.
- `L = Z ⋊ F`, with product `(φ, g)(ψ, h) = (φ + gψ, gh)` and `(gψ)(x) = ψ(g⁻¹x)`.
- `L` acts on `Z` by `(φ, g)·f = φ + gf`.
- For `y ∈ D`, `e_y ∈ Z` is the indicator of `{y}`.

The breakpoint cocycle `c_g = β(g⁻¹)`, the affine action `g ∗ φ = c_g + g·φ` of `F` on `Z^{(D)}`, its freeness, and
`supp c_s = s(B(s))` are taken from Steps 1 and 5 of `thompson-f-amenable-iff-dyadic-action-extensively-amenable-proof`.
Moore's theorem is used only for Corollary 2.

## Step 1. The chain and its return probability

Let `σ` be uniform on `{(0,e), (e_{x_0}, e)}`, and `q = σ ∗ μ ∗ σ` on `L`.
- A sample of `q` is `(a e_{x_0}, e)(0, h)(b e_{x_0}, e) = (a e_{x_0} + b e_{h x_0}, h)`, with `a, b ∈ {0,1}` fair and
  independent of `h ∼ μ`.
- `q` is symmetric, and `|supp q| ≤ 4|Γ|`.

Let `ℓ_k` be i.i.d. `∼ q` with `F`-components `h_k`. Put `f_0 = 0` and `f_n = ℓ_n·f_{n−1}`. Unrolling:

`f_n = Σ_{k=1}^{n} ( a_k e_{g_n g_k⁻¹ x_0} + b_k e_{g_n g_{k−1}⁻¹ x_0} )`.

The positions that occur are exactly `g_n O_n`, and each receives at least one fair bit independent of `(h_k)`.
Conditionally on `(h_k)`, `f_n` is uniform over the subsets of `g_n O_n`. Hence

`P^n(0,0) := P(f_n = 0) = p_n`.

Let `(λ_ℓ u)(z) = u(ℓ⁻¹ z)` on `ℓ²(Z)` and `P = Σ_ℓ q(ℓ) λ_ℓ`. `P` is self-adjoint, `(P^j δ_0)(z) = P(f_j = z)`,
and `P^{2j}(0,0) = ‖P^j δ_0‖₂²`.

## Step 2. An almost invariant unit vector (part L)

Assume `e ∈ Γ` and `p_{2n} ≥ e^{−2δn}`.
- `p_{2n} = Π_{j<n} r_j` with `r_j = P^{2j+2}(0,0)/P^{2j}(0,0)`. So some `j ≤ n−1` has `r_j ≥ e^{−2δ}`.
- Put `f = P^j δ_0 / ‖P^j δ_0‖₂ ≥ 0`. Then `⟨f, P²f⟩ = r_j ≥ 1 − 2δ`.
- For a real unit vector `‖λf − f‖² = 2 − 2⟨f, λf⟩`. So `Σ_ℓ (q∗q)(ℓ) ‖λ_ℓ f − f‖₂² ≤ 4δ`.

Weights:
- `q((0,g)) ≥ μ(g)/4`, taking `a = b = 0`.
- `q((e_{x_0},e)) ≥ μ(e)/2`, taking `h = e` and exactly one of `a, b` equal to `1`.
- Since `(0,e) ∈ supp q` with weight `≥ w/4`, `q∗q ≥ w²/16` on `Γ̃ := {(0,g) : g ∈ Γ} ∪ {(e_{x_0}, e)}`.

Hence `‖λ_ℓ f − f‖₂ ≤ 8√δ/w` for `ℓ ∈ Γ̃`.

## Step 3. The lamp law

Put `ν = f²`, a probability measure on `Z`.
- **Size.** `|supp ν| ≤ (4|Γ|)^n`, and every `φ ∈ supp ν` has `|supp φ| ≤ 2n`.
- **F-invariance.** Namioka's inequality `‖u² − v²‖₁ ≤ ‖u−v‖₂‖u+v‖₂` gives `‖λ_ℓ ν − ν‖₁ ≤ 16√δ/w =: θ` for
  `ℓ ∈ Γ̃`. The `ℓ¹` defect is subadditive along words.
- **Switches at breakpoints.** For `y ∈ B(s)`, `(e_y, e) = (0,g_y)(e_{x_0},e)(0,g_y⁻¹)`. This is a word of length
  at most `2T+1` in `Γ̃`, so `η_y := ‖λ_{(e_y,e)} ν − ν‖₁ ≤ (2T+1)θ`.
- **Coverage.** `(e_y,e)` flips the lamp at `y`. So `ν{φ(y)=0} ≤ (1 + η_y)/2`.

## Step 4. Unions of independent lamp sets

Draw `φ^1, …, φ^M` i.i.d. `∼ ν`, and let `ν_M` be the law of `S = ∪_i supp φ^i` on `P_f(D)`.
- **Size.** `|supp ν_M| ≤ (4|Γ|)^{nM}`, and `k := max |S| ≤ 2nM`.
- **Invariance.** The union map is `F`-equivariant, so `ε₁ := Σ_{s∈Γ} ‖sν_M − ν_M‖₁ ≤ |Γ| M θ`.
- **Coverage.** `ε₂ := Σ_s Σ_{y∈B(s)} ν_M{y ∉ S} ≤ b((1 + (2T+1)θ)/2)^M`.

Take `0 < η ≤ 1`, `M = M_η` and `δ ≤ δ_η`. Then `θ ≤ η/(8|Γ|M_η(2T+1))`, so:
- `ε₁ ≤ η/8`;
- `(2T+1)θ ≤ 1/8`, so the coverage base is `≤ 9/16 < 3/4`;
- `(4/3)^{M_η} ≥ (8b+8)/η`, so `2ε₂ ≤ 2bη/(8b+8) < η/4`.

Hence `ε₁ + 2ε₂ < η/2`.

## Step 5. Push to a Følner set of F

This is the argument of `thompson-f-dyadic-ea-witnesses-need-tower-size-proof`, Steps 1–5, with `C^{−n}` replaced
by `η`. Moore's theorem is not used.

- **Boxes.** Put `N = ⌈2L/η⌉`, which is at least `1` since `L ≥ 1`. For each `S` let `U_S` be uniform on
  `Box(S) = {φ ∈ Z^{(D)} : supp φ ⊆ S, |φ(x)| ≤ N}`, and put `ν' = Σ_S ν_M(S) U_S`. Then
  `|supp ν'| ≤ |supp ν_M|·(2N+1)^k`.
- **Invariance of the boxes.** Suppose `B(s) ⊆ S`. Then `s ∗ U_S` is `U_{sS}` translated by `c_s`, where
  `supp c_s ⊆ sS` and `‖c_s‖₁ = ‖β(s)‖₁`. So `‖s ∗ U_S − U_{sS}‖₁ ≤ 2‖β(s)‖₁/(2N+1)`. Otherwise the defect is
  at most `2`. Summing over `s ∈ Γ`:
  `Σ_s ‖s ∗ ν' − ν'‖₁ ≤ ε₁ + 2ε₂ + 2L/(2N+1) < η/2 + η/2 = η`.
- **Push to F.** Freeness gives an equivariant `π : Z^{(D)} → F`. So `μ' = π_*ν'` has `Σ_s ‖sμ' − μ'‖₁ < η` and
  `|supp μ'| ≤ |supp ν'|`.
- **Level sets.** By layer-cake, some nonempty level set `A` of `μ'` has `Σ_s |sA Δ A| < η|A|`. Then
  `A' = A⁻¹` has `Σ_γ |A'γ Δ A'| < η|A'|`, since `Γ` is symmetric.

So `Føl_Γ(1/η) ≤ |A'| ≤ (4|Γ|)^{nM_η} (4L/η + 3)^{2nM_η} = 2^{n M_η K_η}`, using `2N+1 ≤ 4L/η + 3`. This is part (L).

## Step 6. Part (U): lift a Følner set to the lamplighter

Let `U` be finite nonempty with `Σ_{s∈Γ} |Us Δ U| ≤ η|U|`, and `η ≤ 2`. This step does not need `e ∈ Γ`.

**Return probability on L.** `P(f_{2n} = 0) ≥ P(ℓ_{2n}⋯ℓ_1 = e) = q^{∗2n}(e)`.

**The lifted set.** Let `A = {(φ, g) ∈ L : g ∈ U, supp φ ⊆ U x_0}`, so `|A| = |U| 2^{|Ux_0|} ≤ |U| 2^{|U|}`. Let
`R u(x) = Σ_ℓ q(ℓ) u(xℓ)` on `ℓ²(L)`. `R` is self-adjoint because `q` is symmetric. Put `u = 1_A/√|A|`.

- **The bracket.** For `ℓ = (a e_{x_0} + b e_{hx_0}, h)`, `(φ,g)ℓ = (φ + a e_{gx_0} + b e_{ghx_0}, gh)`. This lies
  in `A` iff `gh ∈ U`, because then `gx_0, ghx_0 ∈ Ux_0`. So `|{x ∈ A : xℓ ∈ A}| = 2^{|Ux_0|} |U ∩ Uh⁻¹|`. Now
  `|U \ Uh⁻¹| = |Uh \ U| = |Uh Δ U|/2`. So
  `⟨u, Ru⟩ = 1 − Σ_h μ(h) |Uh Δ U|/(2|U|) ≥ 1 − η/2 ≥ 0`.
- **Spectral bound.** Let `m` be the spectral measure of `u` for `R`, a probability measure on `[−1,1]`. Jensen gives
  `⟨u, R^{2n} u⟩ = ∫ t^{2n} dm ≥ (∫ t dm)^{2n} = ⟨u,Ru⟩^{2n}`.
- **Upper bound on the bracket.** `⟨u, R^{2n}u⟩ = |A|⁻¹ Σ_{x,y∈A} q^{∗2n}(x⁻¹y)`. By symmetry and Cauchy–Schwarz,
  `q^{∗2n}(z) ≤ ‖q^{∗n}‖₂² = q^{∗2n}(e)`. So `⟨u, R^{2n}u⟩ ≤ |A| q^{∗2n}(e)`.

Hence `p_{2n} ≥ q^{∗2n}(e) ≥ (1 − η/2)^{2n}/|A| ≥ (1 − η/2)^{2n}/(|U|2^{|U|})`. This is part (U).

## Step 7. Corollaries

**Corollary 1, lower bound.** Let `N = N_μ(ε) < ∞`, and put `n' = ⌊N/2⌋ ≥ 1`. Since `O_{2n'} ⊆ O_N`,

`p_{2n'} ≥ 2^{−εN} P(|O_N| < εN) > e^{−2εN} ≥ e^{−2(3ε)n'}`.

Part (L) with `δ = 3ε ≤ δ_η` gives `N ≥ n' ≥ log₂ Føl_Γ(1/η)/(M_η K_η)`.

**Corollary 1, upper bound.** Take `U` with `|U| = Føl_Γ(8/ε)`, so `Σ_s |UsΔU| < (ε/8)|U|`, and let
`n ≥ 4|U|/ε`. Part (U) gives `p_{2n} ≥ (1 − ε/16)^{2n} 4^{−|U|}`.
- `−ln(1−x) ≤ 2x` for `x ≤ 1/2`, so `(1 − ε/16)^{2n} ≥ e^{−εn/4}`.
- `|U| ≤ εn/4`, so `4^{−|U|} ≥ e^{−0.35εn}`.

So `p_{2n} ≥ e^{−0.6εn}`. Then

`P(|O_{2n}| < 2εn) ≥ p_{2n} − 2^{−2εn} ≥ e^{−0.6εn} − e^{−1.38εn}`.

This exceeds `e^{−2εn}` once `e^{0.78εn} > 2`, which holds because `εn ≥ 4`. So every even `N = 2n` with
`n ≥ ⌈4|U|/ε⌉` is a witness.

**Corollary 2.** Moore's Theorem 1.1 gives `Føl_Γ(C^m) ≥ exp_m(0)`, and `e ∈ Γ` does not change the sums. Part (L)
with `η = C^{−m}` and `log₂ exp_m(0) = exp_{m−1}(0)` gives the tower rate.

**Corollary 3.** On the trap event, `2^{−|O_{2n}|} ≥ 2^{−s}`. So `p_{2n} ≥ c 2^{−s} e^{−2λn}` for every `n`. Put
`x = (s ln 2 + ln(1/c))/(2λ)` and `n₁ = max(1, ⌈x⌉) ≤ x + 1`. Then `p_{2n₁} ≥ e^{−2(2λ)n₁}`. Part (L) with
`δ = 2λ ≤ δ_η` gives `x + 1 ≥ log₂ Føl_Γ(1/η)/(M_η K_η)`.

## Scope

- Part (L) and the lower bounds use `e ∈ supp μ`, once, in Step 2. Part (U) holds for every symmetric finitely
  supported generating `μ`.
- All constants depend on `μ` and `x_0`. The comparison is with `Føl_Γ` for `Γ = supp μ`.
- Nothing assumes amenability or non-amenability of `F`.
