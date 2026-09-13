
### 36.3 Relations and algebra-level models (Section 3). PASS

- **Lemma 3.1.** `N_23 N_12 = ψ(s_10 t_11 · s_0 t_10)`, and `t_11 s_0 = t_1 t_1 s_0 = 0`. In a conjugate frame the
  product is `ψ(u · 0 · u^(-1))`.
- **Proposition 3.2, recomputed.**
  - (a) `Φ(s_0 t_10) = t_0 e_01`. `E_01(1) E_10(−1) E_01(1) = e_01 − e_10 = w` and `w e_10 w^(-1) = −e_01`, so
    `E_01(−t_0)` and its inverse `E_01(t_0)` lie in `Φ(<S4>)`.
  - (b) `Φ(s_10 t_11) = s_0 t_1 e_11`, and `s_0 t_1` is a normal-form monomial outside `span{s_0^a t_0^b}`.
  - (c) The `Φ`-entries of the six roots:
    - code `{0, 10, 11}`: `s_0 t_10 -> t_0`, `s_10 t_0 -> s_0`, `s_0 t_11 -> t_1`, `s_11 t_0 -> s_1`,
      `s_10 t_11 -> s_0 t_1`, `s_11 t_10 -> s_1 t_0`;
    - code `{1, 00, 01}`: `s_1 t_00 -> t_0`, `s_00 t_1 -> s_0`, `s_1 t_01 -> t_1`, `s_01 t_1 -> s_1`,
      `s_00 t_01 -> s_0 t_1`, `s_01 t_00 -> s_1 t_0`.

    Only `t_0` and `s_0` lie in `T`, and they come from `{0, 10}` and `{1, 00}`. The roots `x_12` and `x_23` of a code
    frame use the distinct pairs `{c_1, c_2}` and `{c_2, c_3}`.
- **Proposition 3.3, recomputed.**
  - (a) Incomparable `σ, κ` make `s_σ t_κ` square-zero, so `T^(-1) = 1 − λ s_σ t_κ`. `e_ki (λ m e_ij) e_jl = λ m e_kl`
    gives `m I`. Conversely every generator and inverse lies in `M_2(W)`.
  - (b) `Q = 1 − s_0 t_0` lies in `T`, and `ψ(t_0) ψ(s_0) = 1` forces `ψ(Q) = 0`.
    - If `β = 0^(j-1) 1 β''`, then `t_β = t_(β'') t_1 t_0^(j-1)`, and
      `m s_0^(j-1) Q t_0^(j-1) = s_α t_(β'') t_1 s_1 t_1 t_0^(j-1) = m`.
    - The case of `α` is the mirror image.
  - (c) On `K[Ω]` the relations `t_i s_j = δ_ij` and `s_0 t_0 + s_1 t_1 = 1` hold, since every sequence has a first
    letter.
    - If `β` contains a `1`, then `t_β e_(0^∞) = 0`. The line `K e_(0^∞)` is invariant, with `s_0, t_0 -> 1` and
      `m -> 0`.
    - If `β = 0^b` and `α` contains a `1`, then `s_0` and `t_0` preserve `U = span{e_ξ : ξ != 0^∞}`, and `m` sends
      `e_ξ` to `0` or to `e_(αξ')` with `αξ' != 0^∞`. On the one-dimensional quotient `s_0, t_0 -> 1` and `m -> 0`.
    - Otherwise `m = s_0^a t_0^b` lies in `T`, and `χ` is the symbol at `ζ = 1`.

    Over `F_3`, `M_2(χ)` sends `z` to `−I`.
  - (d) `Φ(s_01 t_1) = s_1 e_01` and `Φ(s_1 t_01) = t_1 e_10`, so `W = R`. A nonzero map from the simple algebra `R` is
    injective and keeps `t_0 s_0 = 1 != s_0 t_0`.
- **Corollary 3.4, recomputed.**
  - `t_0 · s_0 t_1 = t_1`, so `W_5 = K<s_0, t_0, t_1>`. Words reduce by `t_0 s_0 = 1` and `t_1 s_0 = 0` to the
    monomials `s_0^a t_ν`.
  - (b) The images of the `e_ij` are matrix units summing to `1`, so `W = M_2(W')`. `W'` is a corner of a weakly finite
    algebra, so it is weakly finite, and `ψ∘Φ^(-1) = M_2(ψ')`. Proposition 3.3(b) with `β = 1` gives `ψ'(s_0 t_1) = 0`.
  - (c) `t_ν s_0^b` is `t_(ν'')` if `ν = 0^b ν''`, is `s_0^(b-c)` if `ν = 0^c` with `c < b`, and is `0` otherwise.
    - So the product of two basis monomials is `s_0^a t_(λν'')`, `s_0^(a+b-c) t_λ` or `0`.
    - `σ_5` is multiplicative in each case, since `|λν''| = |λ| + |ν| − b`, and the value is `0` once `ν` or `λ` has a
      `1`.
    - `σ_5(s_0 t_1) = 0`, so `x_23(1) -> I`.

### 36.4 Weakly finite models with D != 0 (Section 4). PASS

- **Theorem 4.1, recomputed.**
  - `F_3[Γ_0]` is stably finite by `linear-sofic-group-algebra-is-stably-finite` (ESTABLISHED): `Γ_0` is countable,
    and sofic groups are linear sofic.
  - `[z]` is central with `[z]^2 = 1`, so `ε_-^2 = 4(2 − 2[z]) = 2(1 − [z])` mod `3`.
  - A corner at a central idempotent of a stably finite ring is stably finite. `ρ(gh) = ε_-[g] ε_-[h]`, and
    `ε_-[z] = −ε_-`.
  - `x_23(1) x_12(1) = 1 + s_0 t_10 + s_10 t_11`, because `s_10 t_11 s_0 t_10 = 0`.
    - The four elements `1`, `x_12(1)`, `x_23(1)`, `x_23(1) x_12(1)` are `1` plus distinct sums of the independent
      monomials `s_0 t_10` and `s_10 t_11`.
    - Their `z`-multiples have coefficient `−1 != 1` on the monomial `1`.
    - So the eight terms of `D_ρ`, each with coefficient `±2`, are distinct and `D_ρ != 0`.
- **Corollary 4.2.** `ω(0) <= ω(10) = ω(1) + ω(0)`, and `ω(10) <= ω(11)` if and only if `ω(0) <= ω(1)`. `H^ω_≤` is
  countable and sofic (`depth-monotone-leavitt-subalgebras-are-stably-finite`, ESTABLISHED).
- **Theorem 4.3, recomputed.**
  - For large `k`, `F_k` is invariant under `g`, `h` and `gh`, so `(gh)_k = g_k h_k` and `(g^(-1))_k = g_k^(-1)`.
  - `AB = I` in `M_n(Q_3)` means `A_k B_k = I` for all large `k`, so `B_k A_k = I` for all large `k`.
  - `z_k^(⊗3) = (−1)^3 = −1`.
  - `mn = π(s_10 t_11 s_0 t_10) = 0`.
    - `(1 + n)^(⊗3) − 1 = Σ_(S != ∅) n^S`, and `m^T n^S` carries `mn` on `S ∩ T`.
    - Each coordinate lies in `S`, in `T` or in neither, so there are `3^3 − 2^3 − 2^3 + 1 = 12` survivors. Each has
      coefficient `1`, and their patterns in `{1, n, m}^(⊗3)` are distinct.
  - Put `(π(s_μ t_ν) f)(μξ) = f(νξ)`. Then `n 1_[10] = 1_[0]`, `m 1_[10] = 0`, `n 1_[11] = 0` and
    `m 1_[11] = 1_[10]`.
    - So `1`, `n`, `m` are independent, and the `27` elementary tensors in them are independent.
    - So `D_k != 0` for all large `k`, which is `D_(ρ_3) != 0` in `Q_3`.
- **Remark 4.4.**
  - `(gh)^* = h^* g^*`, so `g -> (g^*)^(-1)` is an automorphism of `G`. It exchanges `H^ω_≥` and `H^ω_≤`, and it sends
    `x_12(1)` to `1 − s_10 t_0`.
  - Advisory 3 in 36.5 concerns this remark's wording.
