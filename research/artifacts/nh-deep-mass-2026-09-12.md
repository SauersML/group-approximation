# Deep non-unit root mass vanishes under vertex rounding: two compressor attractors (2026-09-12)

Lane `nh-deep-mass`, swarm 3. Target: `vertex-rounding-deep-nonunit-root-mass-vanishes`. Read at `fbcba57d8`.
Nothing here is reviewed.

## 0. Result and why the drift obstruction does not apply

**Theorem.** In the setting of the target, `μ_n(depth_nu > 1) -> 0` along `U`, with no rate.

- **Depth is one coordinate of a shape.** The Attempts of the target track only the depth, on which
  compressor and torus act by an amenable drift. The compressor also acts on the axis extents
  `e_i` (nilpotency orders of the `x_i` in the origin factor). Iterating a compressor collapses the ratio
  `e_1/e_d` of every deep character to one value fixed by its left Perron vector.
- **Two attractors.** `A = (min(i,j))` and its reversal conjugate `B` have different attracting ratios.
  So their transported copies of `μ_n` concentrate on disjoint sets of characters, which caps the deep
  mass at a fixed fraction plus an error that vanishes along `U`.
- **The containment is overcome at character level.** `J_κ ⊇ φ_A^(-1) J_ρ` only bounds shapes from
  above. The missing lower bound comes from the invariance of `μ_n` under scaling by units of `B_n`
  (Lemma 1) and a chain rank bound in a local ring (Lemma 2).

## 1. Setting

- `R_+ = F_q[x_1..x_d]`, `Γ = EL_r(R_+) < G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)`, `r, d >= 3`. `σ` is
  trace-preserving with (H1) roundings `π_n`.
- By item 1 of `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`, `π_n` factors through
  `St_r(B_n)`, where `B_n = R_+/I_n` is finite.
- Characters of `(R_+, +)` killing `I_n` are `χ = ψ ∘ λ`, with `λ : R_+ -> F_q` linear and `ψ` a fixed
  nontrivial character of `(F_q, +)`. For an `F_q`-subspace `W`, `χ(W) = 1` iff `λ(W) = 0`.
- **Origin characters.** By item 1 of `vertex-rounding-non-unit-mass-at-origin`, constituents with an
  intermediate local factor have trace `-> 0`. Their root spectra contain every character whose non-unit
  component meets an intermediate place, so that spectral mass also tends to 0. Every other character is
  `χ = χ_u · χ_0`, where `χ_u` is of unit type and `χ_0 = ψ ∘ λ_0` kills an ideal whose quotient is local
  at `m_0 = (x_1..x_d)`. Write `A_0` for the origin factor of `B_n`.
- **Shape.** `J(χ_0)` is the largest ideal in `ker λ_0`. `Sh(χ_0) = {a ∈ N^d : λ_0(x^a R_+) ≠ 0}` is finite and
  down-closed, and it is the set of exponents of monomials outside `J(χ_0)`. Then
  `depth_nu(χ) = 1 + max{c : c·(1,..,1) ∈ Sh}` and `e_i(χ) = max{c : c e_i ∈ Sh}`.
- **Transport.** For nonnegative `M ∈ SL_d(Z)`, `D_M χ = χ ∘ φ_M`. It acts componentwise:
  `D_M χ = (χ_u ∘ φ_M)·(χ_0 ∘ φ_M)`, a unit-type character times an origin character. So
  `(D_M χ)_0 = D_M χ_0`.

## 2. Lemma 1: unit scaling

For `u ∈ B_n^×`, `μ_n` is invariant under `χ -> χ(u ·)`.

*Proof.*
- In `St_r(B_n)`, `h_31(u) = w_31(u) w_31(-1)` conjugates `x_12(f)` to `x_12(u^(±1) f)` for every `f`. These are
  the conjugation formulas for `w_ij(u)` (Milnor, *Introduction to Algebraic K-Theory*, §9). In `GL_r` this
  is conjugation by a diagonal matrix.
- `π_n(St_r(B_n)) = π_n(Γ)`. So `f -> π_n(e_12(u f))` is unitarily conjugate to `f -> π_n(e_12(f))` by one
  fixed unitary, and the spectral measure is invariant.

**Disintegration.** Let `U_0 = {1} × A_0^×` act through the origin factor. Then
`μ_n = ∫ Unif(U_0 · χ) dμ_n(χ)`. `Sh`, `depth_nu` and each `e_i` are `U_0`-invariant, because
`u x^a R = x^a R` in a local ring when `u` is a unit.

## 3. Lemma 2: transport of shapes

Let `M ∈ SL_d(Z)` be nonnegative, `w ∈ N^d ∖ 0`, `c ∈ N`, and `χ_0` an origin character.

(a) **Upper bound, deterministic.** If `c w ∈ Sh(D_M χ_0)`, then `c M w ∈ Sh(χ_0)`.

(b) **Lower bound, over the orbit.** Suppose `c M w ∈ Sh(χ_0)` and put
`ℓ = max{j >= 0 : (c+j) M w ∈ Sh(χ_0)}`. For `u` uniform in `A_0^×`,

```text
P( c w ∉ Sh(D_M(χ_0(u ·))) )  <=  2 q^(-(ℓ+1)).
```

*Proof of (a).* `φ_M(x^(cw) R_+) = x^(cMw) φ_M(R_+) ⊆ x^(cMw) R_+`.

*Proof of (b).*
- **The event is a kernel.** The event says `λ_0(u · x^(cMw) φ_M(g)) = 0` for all `g`. So `u ∈ ker Λ`, where
  `Λ : A_0 -> F_q^(N^d)` is the linear map `u -> (λ_0(u x^(cMw + Mb)))_(b ∈ N^d)`.
- **Rank.** Put `y = x^(Mw) ∈ m_0` and `h_j = x^(cMw) y^j` for `0 <= j <= ℓ`. The functionals `u -> λ_0(u h_j)` are
  coordinates of `Λ`, and they are independent.
  - Suppose `Σ α_j λ_0(u h_j) = 0` for all `u`. Then `g = Σ α_j h_j` satisfies `λ_0(g R_+) = 0`, so `g ∈ J(χ_0)`.
  - Let `j_0` be the least index with `α_(j_0) ≠ 0`. Then `g = h_(j_0)(α_(j_0) + y s)`.
  - `R_+/J(χ_0)` is local and `y` is nilpotent there, so the second factor is a unit. Hence `h_(j_0) ∈ J(χ_0)`,
    i.e. `(c+j_0) M w ∉ Sh(χ_0)`. That contradicts `j_0 <= ℓ` and down-closedness.
- **Count.** So `rank Λ >= ℓ + 1`, and `P(u ∈ ker Λ) = q^(-rank Λ)` for `u` uniform in `A_0`. Conditioning on
  units multiplies this by `|A_0|/|A_0^×| = q/(q-1) <= 2`, since `A_0` is local with residue field `F_q`.

## 4. Lemma 3: Perron sandwich

- **Perron data.** Let `A ∈ SL_d(Z)` have every entry `>= 1`, with Perron root `λ > 1`, right vector `v > 0` of
  maximum entry 1, and left vector `ℓ > 0` with `ℓ^T v = 1`.
- **Error term.** `A^k = λ^k (v ℓ^T + E_k)` with `||E_k||_max <= C θ^k` for some `θ < 1`. Put
  `γ_k = C θ^k / (min v · min ℓ)`. Entrywise, `(1-γ_k) ℓ_i λ^k v <= A^k e_i <= (1+γ_k) ℓ_i λ^k v`.
- **Scale.** For finite down-closed `Sh`, let `s = sup{t : ⌊t v⌋ ∈ Sh}`, so `⌊t v⌋ ∈ Sh` iff `t < s`. Since
  `v <= (1,..,1)`, `s >= depth`.
- **Statement.** Put `c_i = max{c ∈ N : c A^k e_i ∈ Sh}`. Then

  ```text
  s / ((1+γ_k) ℓ_i λ^k) - 1  <=  c_i  <=  s / ((1-γ_k) ℓ_i λ^k).
  ```

*Proof.*
- **Upper.** If `c A^k e_i ∈ Sh`, then `⌊c(1-γ_k) ℓ_i λ^k v⌋ <= c A^k e_i`, which lies in `Sh`. So
  `c(1-γ_k)ℓ_i λ^k < s`.
- **Lower.** If `c(1+γ_k)ℓ_i λ^k < s`, then `c A^k e_i` is an integer vector below `⌊c(1+γ_k)ℓ_i λ^k v⌋ ∈ Sh`.
  So `c <= c_i`.

## 5. Proof of the theorem

**Compressors.**
- `A_ij = min(i,j)`. `A = L L^T` with `L` the lower unitriangular all-ones matrix, so `det A = 1`. Every entry is
  `>= 1`, and `A` is symmetric, so `ℓ_A = v_A`.
- `λ v_d = Σ_j j v_j > Σ_j v_j = λ v_1`, so `ℓ_(A,d) > ℓ_(A,1)`. Put `β = log(ℓ_(A,d)/ℓ_(A,1)) > 0`.
- `B = P A P^(-1)`, with `P` the reversal permutation. It has every entry `>= 1`, `det B = 1`, the same `λ`, `C`
  and `θ`, and `ℓ_B = P ℓ_A`. So `log(ℓ_(B,d)/ℓ_(B,1)) = -β`.

**Parameters.**
- Fix `k` with `log((1+γ_k)/(1-γ_k)) < β/4`. Put `M_+ = A^k`, `M_- = B^k`, `Λ = λ^k` and
  `N = ||A^k 1||_∞ = ||B^k 1||_∞`.
- Fix `L >= 1`. Choose `K` with `-log(1-ε) < β/4`, where `ε = (L+1)(1+γ_k) Λ max_i ℓ_i / K`, and with
  `K' = ⌊(K-1)/N⌋ - L + 1 >= 2`.
- For an origin character with `e_1, e_d >= 1`, put `ρ(χ) = log(e_1(χ)/e_d(χ))`. All sets below consist of
  characters whose non-unit component is at the origin.

**Sets.** `E_± = {χ : depth_nu(χ) >= K', ±ρ(χ_0) > β/2}`. They are disjoint, and both lie in `{depth_nu >= K'}`.

**Transported deep characters land in `E_±`.** Let `depth_nu(χ) >= K`, `M = M_+`, and `s = s(Sh(χ_0)) >= K`.
- **Upper.** Lemma 2(a) with `w = e_i`, then Lemma 3: `e_i(D_M χ_0) <= c_i <= s/((1-γ_k) ℓ_i Λ)`.
- **Lower.** Lemma 2(b) with `w = e_i` and `c = c_i - L`, so that `ℓ >= L`. Except with orbit probability
  `<= 2q^(-(L+1))`,

  ```text
  e_i(D_M χ_0)  >=  c_i - L  >=  s/((1+γ_k) ℓ_i Λ) - (L+1)  >=  (1-ε) · s/((1+γ_k) ℓ_i Λ),
  ```

  for `i = 1` and `i = d`.
- **Depth.** Lemma 2(b) with `w = (1,..,1)` and `c = c^(1) - L`, where `c^(1) = max{c : c M 1 ∈ Sh} >= ⌊(K-1)/N⌋`.
  Except with orbit probability `<= 2q^(-(L+1))`, `depth_nu(D_M χ) >= K'`, and then `e_1, e_d >= K' - 1 >= 1`.
- **Ratio.** On the good event,
  `ρ(D_M χ_0) >= log(ℓ_d/ℓ_1) - log((1+γ_k)/(1-γ_k)) + log(1-ε) > β - β/4 - β/4 = β/2`.
  So `D_M χ ∈ E_+`.
- **Mass.** `{depth_nu >= K}` is `U_0`-invariant. By the disintegration of Lemma 1,
  `μ_n({depth_nu >= K} ∖ D_(M_+)^(-1) E_+) <= 6 q^(-(L+1))`. The same holds for `M_-` and `E_-`.

**Counting.**
- `M_±` are compressors, so `compressor-transport-exactifies-under-vertex-rounding` gives
  `|μ_n(E) - μ_n(D_(M_±)^(-1) E)| <= η_n^± -> 0` for every Borel `E`. Hence
  `μ_n(E_±) >= μ_n(depth_nu >= K) - 6 q^(-(L+1)) - η_n^±`.
- Add the two inequalities. Since `E_+ ∩ E_- = ∅` and both lie in `{depth_nu >= K'}`,

  ```text
  2 μ_n(depth_nu >= K) - 12 q^(-(L+1)) - η_n^+ - η_n^-  <=  μ_n(depth_nu >= K)  +  μ_n(K' <= depth_nu < K).
  ```

**Conclusion.** Let `ν_n` be the root mass at intermediate places. Then

```text
μ_n(depth_nu > 1)  <=  ν_n  +  2 μ_n(1 < depth_nu < K)  +  12 q^(-(L+1))  +  η_n^+  +  η_n^-.
```

- `ν_n -> 0` by item 1 of `vertex-rounding-non-unit-mass-at-origin`.
- `μ_n(1 < depth_nu < K) <= ⌈log_d K⌉·η_n` by item 3 of `nonunit-component-root-mass-is-log-scale-folner`.
- So `lim_U μ_n(depth_nu > 1) <= 12 q^(-(L+1))` for every `L`, i.e. it is 0. ∎

## 6. Consequences and status

- **The target is proved from established claims.** The route is `deep-nonunit-root-mass-two-attractor-proof`.
  Neither the Laurent torus nor the shallow claim is used.
- **Theorem E.** The fifth premise of `theorem-e-vertex-unit-type-via-deep-root-mass` is settled. That route is
  now open only through (H1), `hs-stable-vertex-rounding-for-every-model`.
- **Reading with `log-depth-rate-rounding-is-equivalent-to-unit-type`.** Under (H1), every rounding family of
  the Theorem E actor becomes unit type after trivializing its non-unit constituents.
- **Where the Attempts went wrong.**
  - The drift obstruction is correct for depth alone. Shape ratios supply the missing invariant.
  - The containment `J_κ ⊇ φ_A^(-1) J_ρ` holds for constituents. The lower bound holds only for orbit-typical
    characters, which is all TV invariance needs.
- **Quantitative remark.** `k` depends only on `d`, and `K = O_d(L+1)`. So
  `μ_n(depth_nu > 1) <= ν_n + O_d(log L)·max(η_n, η_n^±) + 12 q^(-L)`, which gives a rate polylogarithmic in the
  defects. It is not recorded as a claim.
