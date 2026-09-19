---
rg: 2
id: lifted-thompson-t-haagerup-iff-twist-cost-spectral-measure-proof
kind: route
title: Compactness of normalized positive definite functions with prescribed z-twist, a spectral Fatou argument for necessity, and Hahn-Banach lifting of nu to the space of twisted states for sufficiency
target: lifted-thompson-t-haagerup-iff-twist-cost-spectral-measure
requires:
  - lifted-thompson-t-relative-t-forces-dyadic-twist-gap
  - haagerup-splits-as-coset-plus-subgroup-properness
  - thompson-v-has-haagerup-property
  - lifted-thompson-t-quotients-are-rotation-centralizers
---

**Imported standard facts.**
- (CND) For a unitary `π` and vector `ξ`, `g ↦ ‖π(g)ξ − ξ‖²` is cnd. Nonnegative sums and
  integrals of cnd functions, when finite, are cnd. `√ψ` is subadditive for cnd `ψ`, so
  `ψ(g) ≤ |g|_S² max_{s∈S} ψ(s)`. (Bekka–de la Harpe–Valette, *Kazhdan's property (T)*, §C.2.)
- (Sch) Schoenberg: if `ψ` is cnd then `e^{−tψ}` is positive definite for `t > 0` (BdHV, C.3.2).
- (GNS) A positive definite `φ` with `φ(e) = 1` is `⟨π(·)ξ, ξ⟩` for a cyclic unit vector `ξ`.
- (Sp) For a unitary `U` and a vector `ξ` there is a finite Borel measure `μ` on `R/Z` with
  `⟨U^n ξ, ξ⟩ = ∫ e(nθ) dμ` and `‖ξ‖² = μ(R/Z)`. Spectral projections `E(A)` of `U` commute
  with every operator commuting with `U`.
- (HB) Hahn–Banach with norm preservation, and the Riesz representation theorem on a compact
  metric space. A real functional `ℓ` on `C(K)` with `‖ℓ‖ = ℓ(1)` is positive: for
  `0 ≤ h ≤ 1`, `ℓ(1 − h) ≤ ‖ℓ‖·‖1 − h‖ ≤ ℓ(1)`, so `ℓ(h) ≥ 0`.

**Step 0. Twisted states.**
- Let `PD_1` be the set of positive definite `φ : T̄ → C` with `φ(e) = 1`. It is compact and
  metrizable in the pointwise topology, since `T̄` is countable.
- Let `P = {(θ, φ) ∈ R/Z × PD_1 : φ(zg) = e(θ) φ(g) for all g}`. It is closed, hence compact.
- Let `F(θ, φ) = max_{s∈S} (2 − 2 Re φ(s))^{1/2}`. It is continuous on `P`.
- **Claim 0.** `c(θ) = min { F(θ, φ) : (θ, φ) ∈ P }`, and the minimum is attained.
  - If `π(z) = e(θ) I` and `ξ` is a unit vector, `φ = ⟨π(·)ξ, ξ⟩` lies in `P_θ`, and `F(θ, φ)`
    is the cost `max_s ‖π(s)ξ − ξ‖`.
  - Conversely, for `(θ, φ) ∈ P` the GNS vector satisfies `⟨π(g)ξ, π(z)^*ξ⟩ = φ(zg) = e(θ)φ(g)`,
    so `π(z)ξ = e(θ)ξ`. As `z` is central and `ξ` cyclic, `π(z) = e(θ) I`.
  - The fibre `P_θ` is compact and `F` continuous, so the infimum is attained.
- `c` is lower semicontinuous (part (a) of `lifted-thompson-t-relative-t-forces-dyadic-twist-gap`,
  and also directly from Claim 0), hence Borel. It vanishes only at `0`.

**Step 1. Reduction to the centre.**
- `T ≤ V` (Cannon–Floyd–Parry), and Haagerup passes to subgroups, so `T` has a proper cnd
  function by `thompson-v-has-haagerup-property`. Pulled back along `T̄ → T̄/⟨z⟩ = T`, it is cnd
  on `T̄` and proper modulo `⟨z⟩`.
- By `haagerup-splits-as-coset-plus-subgroup-properness` with `H = ⟨z⟩`, `T̄` is Haagerup iff some
  cnd function on `T̄` is proper on `⟨z⟩`.

**Step 2. Local lower bound.** For `θ_0 ∈ R/Z` and `ε > 0` there is `δ > 0` such that:
whenever `π` is unitary, the spectrum of `π(z)` lies in the closed arc of radius `δ` about `θ_0`,
and `ξ` is a unit vector, we have `max_s ‖π(s)ξ − ξ‖ ≥ c(θ_0) − ε`.
- Suppose not. Then there are `π_n`, radii `δ_n → 0` and unit `ξ_n` with cost at most
  `c(θ_0) − ε`.
- Put `φ_n = ⟨π_n(·)ξ_n, ξ_n⟩` and pass to a pointwise limit `φ ∈ PD_1`.
- By the spectral theorem, `‖π_n(z) − e(θ_0)‖ ≤ 2π δ_n`. Hence
  `|φ_n(zg) − e(θ_0) φ_n(g)| = |⟨π_n(g)ξ_n, (π_n(z)^* − e(−θ_0))ξ_n⟩| ≤ 2π δ_n`.
- In the limit, `(θ_0, φ) ∈ P` and `F(θ_0, φ) ≤ c(θ_0) − ε`. This contradicts Claim 0.

**Step 3. Spectral Fatou inequality.** Let `π` be any unitary representation of `T̄`, `ξ` a
vector, and `μ` the spectral measure of `π(z)` at `ξ`. Then
`∫ c(θ)² dμ(θ) ≤ Σ_{s∈S} ‖π(s)ξ − ξ‖²`.
- Let `𝒫_m` be the partition of `R/Z` into the `2^m` half-open dyadic arcs `A`.
  Put `ξ_A = E(A)ξ`, so `‖ξ_A‖² = μ(A)`.
- `E(A)` commutes with `π(T̄)` by (Sp), since `z` is central. Hence
  `‖π(s)ξ − ξ‖² = Σ_A ‖π(s)ξ_A − ξ_A‖²`.
- On `E(A)H`, the spectrum of `π(z)` lies in the closure `Ā`. Let `γ(A)` be the infimum of the
  cost over all such representations and unit vectors. Then
  `Σ_s ‖π(s)ξ − ξ‖² ≥ Σ_A max_s ‖π(s)ξ_A − ξ_A‖² ≥ Σ_A γ(A)² μ(A) = ∫ g_m² dμ`,
  where `g_m = γ(A)` on `A`.
- Fix `θ`. The arc of `𝒫_m` containing `θ` has closure inside the closed arc of radius `2^{-m}`
  about `θ`. By Step 2, `liminf_m g_m(θ) ≥ c(θ) − ε` for every `ε > 0`.
- Fatou's lemma gives `∫ c² dμ ≤ liminf_m ∫ g_m² dμ ≤ Σ_s ‖π(s)ξ − ξ‖²`.

**Step 4. (A), necessity.** Suppose `T̄` is Haagerup.
- Take a proper cnd `ψ`, scaled so that `ψ(s) ≤ 1` for `s ∈ S`.
- For `j ≥ 1` put `t_j = 4^{-j}`. By (Sch) and (GNS), `e^{−t_j ψ} = ⟨π_j(·)ξ_j, ξ_j⟩` with
  `ξ_j` a unit vector. Let `μ_j` be the spectral measure of `π_j(z)` at `ξ_j`. Then
  `μ̂_j(n) = e^{−t_j ψ(z^n)}`.
- By Step 3,
  `∫ c² dμ_j ≤ Σ_s ‖π_j(s)ξ_j − ξ_j‖² = Σ_s 2(1 − e^{−t_j ψ(s)}) ≤ 2|S| 4^{-j}`.
- Let `ν` be `Σ_j 2^j μ_j` restricted to `(R/Z) ∖ {0}`. Then `∫ c² dν ≤ 2|S| Σ_j 2^{-j} < ∞`.
  `ν` is σ-finite: it is finite on each `{θ : |e(θ) − 1| ≥ 1/m}`, since `c ≥ 1/(mL)` there.
- The atom at `0` contributes nothing to `|e(nθ) − 1|²`, so
  `Φ_ν(n) = Σ_j 2^j ∫ |e(nθ) − 1|² dμ_j = Σ_j 2^j · 2(1 − e^{−4^{-j} ψ(z^n)})`.
- If `ψ(z^n) ≥ 4`, let `j` be largest with `4^j ≤ ψ(z^n)`. That term alone is at least
  `2^j · 2(1 − e^{−1}) ≥ 2^j ≥ √ψ(z^n) / 2`.
- `ψ` is proper on `⟨z⟩`, so `Φ_ν(n) → ∞`.

**Step 5. (A), sufficiency.** Let `ν` be admissible with `Φ_ν(n) → ∞`.
- *An open set of good states.* Let `U = {(θ, φ) ∈ P : F(θ, φ) < 2c(θ)}`.
  - `2c(θ) − F(θ, φ)` is lower semicontinuous, so `U` is open in the compact metrizable `P`.
    Hence `U = ∪_m K_m` with `K_m` compact and increasing.
  - Since `c(0) = 0`, `U` misses `θ = 0`.
  - For `θ ≠ 0` we have `c(θ) > 0`, so a minimizer from Claim 0 lies in `U`.
  - So the compact sets `A_m = pr(K_m)` cover `(R/Z) ∖ {0}`.
- *Cutting `ν` into finite pieces.* Let
  `D_{m,q} = (A_m ∖ ∪_{i<m} A_i) ∩ {1/q ≤ |e(θ) − 1| < 1/(q−1)}`, with `1/0 = ∞`.
  These are disjoint Borel sets covering `(R/Z) ∖ {0}`. Each has finite `ν`-measure, because
  `c ≥ 1/(qL)` on it.
- *Lifting each piece.* Fix `D = D_{m,q}` and the projection `p : K_m → A_m`, which is onto.
  - `f ↦ f∘p` embeds `C(A_m, R)` isometrically in `C(K_m, R)`.
  - On that subspace `ℓ(f∘p) = ∫_D f dν` has `‖ℓ‖ = ℓ(1) = ν(D)`.
  - A norm-preserving Hahn–Banach extension is positive by (HB). By Riesz it is a finite
    measure `λ_D` on `K_m` with `p_* λ_D = ν|_D`.
- Put `λ = Σ_D λ_D`, a measure on `U` with `pr_* λ = ν`.
- *The cnd function.* Define `ψ(g) = ∫ (2 − 2 Re φ(g)) dλ(θ, φ)`.
  - The integrand is continuous in `(θ, φ)` and is cnd in `g`: it is `‖π_φ(g)ξ_φ − ξ_φ‖²`.
  - On `U`, `2 − 2 Re φ(s) ≤ F(θ, φ)² < 4c(θ)²`. So `ψ(s) ≤ 4 ∫ c² dν < ∞` for `s ∈ S`.
  - By (CND), `ψ` is finite everywhere and cnd.
  - On `P`, `φ(z^n) = e(nθ)`. So `ψ(z^n) = ∫ |e(nθ) − 1|² dν = Φ_ν(n) → ∞`.
- So `ψ` is proper on `⟨z⟩`, and `T̄` is Haagerup by Step 1.

**Step 6. (B), (C) and (D).**
- *(B).* We may drop finitely many terms and assume `θ_1 ≤ 1/2`.
  - Put `c_k = c(θ_k)` and `R_k = Σ_{j≥k} c_j²`.
  - Put `w_k = R_k^{−1/2}`, or `w_k = k` once `R_k = 0`. Then `w_k` is nondecreasing and
    `w_k → ∞`.
  - `Σ w_k c_k² < ∞`, because `(R_k − R_{k+1}) / √R_k ≤ 2(√R_k − √R_{k+1})`.
  - Let `ν = Σ_k w_k δ_{θ_k}`. It is admissible.
  - Given `n` with `|n| θ_1 > 1/2`, let `k` be least with `|n| θ_k ≤ 1/2`. Then
    `|n| θ_k ≥ |n| θ_{k−1} / 2 > 1/4`, so `|e(nθ_k) − 1|² ≥ 2` and `Φ_ν(n) ≥ 2 w_k`.
  - For fixed `J`, once `|n| > 1/(2θ_J)` we get `k > J`. So `Φ_ν(n) → ∞`.
  - Apply (A). The case `θ_k = 2^{-k}` has ratio exactly `1/2`.
- *(C).* `ι_k(T̄) = C_T(r_k)` commutes with `r_k`. So `H_k = ker(ρ_k(r_k) − e(2^{-k}))` is
  invariant under `π_k = ρ_k ∘ ι_k`, and `π_k(z) = ρ_k(r_k) = e(2^{-k})` on `H_k`. Hence
  `c(2^{-k}) ≤ max_s ‖ρ_k(ι_k(s))ξ_k − ξ_k‖`, and (B) applies.
- *(D).*
  - The first bullet: `liminf c > 0` along dyadics makes `Σ c(2^{-k})² = ∞`.
  - The second bullet is (B).
  - The third bullet is the negation of (A).
