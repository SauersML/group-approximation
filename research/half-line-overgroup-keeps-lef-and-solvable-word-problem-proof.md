---
rg: 2
id: half-line-overgroup-keeps-lef-and-solvable-word-problem-proof
kind: route
title: A permutation intertwining the partial level shift of a finite power of a finite model gives finite models of every ball, and levelwise normal forms decide the word problem
target: half-line-overgroup-keeps-lef-and-solvable-word-problem
requires: [groups-embed-in-derived-subgroup-of-half-line-overgroup]
artifacts:
  - research/artifacts/sk-decidable-host-2026-09-13.md
---

From `groups-embed-in-derived-subgroup-of-half-line-overgroup`:
- `C(Γ) = E ⋊ ⟨σ⟩`, where `E` is the sequences `Z → Γ` trivial at `-∞` and eventually constant, acting levelwise;
- `σ f σ^(-1) = φ(f)` with `φ(f)(m) = f(m-1)`, so `(fσ^k)(gσ^l) = (f·φ^k g)σ^(k+l)`.

**Balls.** By induction on length, every `g ∈ B_r` is `fσ^k` with `|k| ≤ r`, `f = e` below `-r`, `f` constant from `r`,
and all values in `B_r(Γ)`. Appending `h_s^(±1)` multiplies the levels `m ≥ k` by `s^(±1)`.

**Models.** Let `ψ : B_(2r)(Γ) → Q` be injective and multiplicative on pairs with product in `B_(2r)(Γ)`.
- `M = 3r`, `H = Q^I` with `I = {-M,…,M}`.
- `A = {v : v_(M-1) = v_M}`, `B = {v : v_(-M) = e}`, and `θ : A → B` with `θ(v)_(-M) = e`, `θ(v)_m = v_(m-1)`, an
  isomorphism.
- Right transversals `H = ⊔ A x_i = ⊔ B y_i` (equal numbers) give `t(a x_i) = θ(a) y_i`, a bijection with
  `t(ax) = θ(a) t(x)`.
- On `Ω = H × Z/5r` put `λ(v)(x,i) = (vx,i)` and `τ(x,i) = (t(x), i+1)`. Then `τ λ(a) τ^(-1) = λ(θ(a))` for `a ∈ A`.
- `Ψ(fσ^k) = λ(ιf) τ^k`, with `ιf = (ψ f(m))_(m∈I)`, on `B_(2r)`.

**Shifts.** If `f = e` below `-2r`, `f` is constant from `2r`, and `|k| ≤ r`, then every intermediate shift `ιφ^j f`
(`0 ≤ j < |k|`) lies in `A` (for `k > 0`), resp. `B` (for `k < 0`), because `2r + j ≤ M - 1` and `-2r - j > -M`. So
`τ^k λ(ιf) τ^(-k) = λ(ιφ^k f)`.

**Partial homomorphism.** For `g = fσ^k`, `g' = f'σ^(k')` in `B_r`:
`Ψ(g)Ψ(g') = λ(ιf · ιφ^k f') τ^(k+k') = Ψ(gg')`, since coordinatewise both factors lie in `B_r(Γ)` and the product
lies in `B_(2r)(Γ)`.

**Injectivity.** The second coordinate recovers `k` (`|k| ≤ r < 5r/2`). Then `ψ` recovers `f` on `I`, and outside `I`
the sequences are trivial or constant.

So `C(Γ)` is LEF, and the converse holds through `δ_0`.

**Word problem.** For a word with `σ`-exponent sum `k` and letters `h_(s_i)^(ε_i)` at prefix exponents `j_i`,
`f(m) = ∏_(j_i ≤ m) s_i^(ε_i)` in order. The word is trivial iff `k = 0` and `f(j_i) = e` for all `i`, which is
decided with `WP(Γ)`. Conversely `δ_0(s) = [σ, h_s^(-1)]` gives `WP(Γ) ≤_m WP(C(Γ))`.

Full proof, remarks and model tests: artifact §§1–3 and §6.
