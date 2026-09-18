---
rg: 2
id: jacobson-head-concentrates-on-template-constituents-proof
kind: route
title: Push the generators into a derived subgroup by commutator words, then split constituent by constituent - scalar relators give a finite projective image of St_4(J) that kills x_12(Q) exactly, and a far non-scalar relator pays for the head out of the defect
target: jacobson-head-concentrates-on-template-constituents
requires:
  - jacobson-head-dies-in-gapped-finite-group-models
  - steinberg-finite-presentation-and-kazhdan-theorem
  - cohn-elementary-group-is-not-lef
  - constituent-gapped-finite-groups-closed-under-products
  - fp-simple-groups-have-no-models-through-classical-products
---

Notation as on the target. All norms are normalized Hilbert-Schmidt norms. For unitaries:
- `‖UA‖_2 = ‖AU‖_2 = ‖A‖_2`;
- `‖U_1⋯U_m - V_1⋯V_m‖_2 <= Σ ‖U_i - V_i‖_2`;
- `min_{|λ|=1} ‖U - λ‖_2² = 2 - 2|tr U|`, and `‖U - 1‖_2² = 2 - 2 Re tr U`.

For a word `w` over `X^±` and unitaries `(A_x)_{x∈X}`, `w(A)` is the evaluation, with `x^(-1)` evaluated as `A_x^(-1)`.
Evaluation is a homomorphism `F(X) → U(N)`, and the same holds for evaluation in `G`.

## Step 0. Fixed data

Imported facts:
- `Λ = St_4(J)` is finitely presented (`steinberg-finite-presentation-and-kazhdan-theorem`, as used in Step 6 of
  `jacobson-head-dies-in-gapped-finite-group-models-proof`). Fix a finite presentation `<X | R>`.
- `μ = x_12(Q)` lies in the kernel of every homomorphism from `Λ` to a finite group. This is the Steinberg chain in
  Step 6 of the same route (from `cohn-elementary-group-is-not-lef`). Also `[μ, ν] = x_13(Q)` with `ν = x_23(1)`.
- `Λ` is perfect: `x_ij(a) = [x_ik(a), x_kj(1)]` for `k ∉ {i,j}`.

Fixed words:
- a word for each `r ∈ R`, and words `u`, `v` over `X^±` representing `μ`, `ν`;
- for each `x ∈ X` a word `v_x ∈ F(X)^(L)` with `v_x = x` in `Λ`. Since `Λ = Λ^(L)`, write `x` as a product of
  commutators of elements of `Λ`, write each of those as a product of commutators, repeat `L` times and spell out
  the result (as in Step 1 of `fp-simple-groups-have-no-models-through-classical-products-proof`). For `L = 0` take
  `v_x = x`;
- for each `x`, an expression `v_x x^(-1) = Π_{i=1}^{M_x} g_i r_i^{±1} g_i^(-1)` in `F(X)` with `r_i ∈ R`. It exists since
  `v_x x^(-1)` lies in the normal closure of `R`.

Put `a = ιμ`, `a' = ιμ^(-1)`, `b = ιν`, `b' = ιν^(-1)`, so `z = ι[μ,ν] = a b a' b'`. `F_1 ⊆ Γ` consists of:
- `1`, `ι(x)` and `ι(x^(-1))` for `x ∈ X`;
- the `ι`-images of all prefixes of the relator words and of `u` and `v`;
- `a'`, `b'`, `ab` and `aba'`.

`δ = def_{F_1}(π)`. All constants below depend only on this fixed data, on `θ` and on `L`.

## Step 1. Word estimates in the original model

Put `U_x = π(ιx)` for `x ∈ X`.
- (E1) `‖π(1) - 1‖_2 = ‖π(1)π(1) - π(1)‖_2 <= δ`.
- (E2) If `g, g' ∈ F_1` and `gg' = 1`, then `‖π(g)π(g') - 1‖_2 <= 2δ`, so `‖π(g') - π(g)^(-1)‖_2 <= 2δ`. This applies to
  `(ιx, ιx^(-1))`, `(a, a')` and `(b, b')`.
- (E3) Let `w = s_1⋯s_m` be a word whose prefixes `p_i` have `ι p_i ∈ F_1`. Then `‖w(U) - π(ιw)‖_2 <= (3m + 1)δ`.
  - Base: `‖1 - π(1)‖_2 <= δ` by (E1).
  - Step: `p_i(U) = p_(i-1)(U) U_(s_i)^±`. Replace `p_(i-1)(U)` by `π(ιp_(i-1))` (induction), then `U_x^(-1)` by
    `π(ιx^(-1))` (at most `2δ`, by (E2)), then `π(ιp_(i-1))π(ιs_i)` by `π(ιp_i)` (at most `δ`, since both factors lie in
    `F_1`).
- Relators: `ι r = 1`, so `‖r(U) - 1‖_2 <= (3|r| + 2)δ`.
- Head: (E3) along `(a,b)`, `(ab,a')`, `(aba',b')` gives `‖π(z) - π(a)π(b)π(a')π(b')‖_2 <= 3δ`. Replace `π(a')` by
  `π(a)^(-1)` and `π(b')` by `π(b)^(-1)` (at most `2δ` each, (E2)). Replace `π(a)` by `u(U)` and `π(b)` by `v(U)`, in both
  the factor and its inverse (at most `(3|u|+1)δ` and `(3|v|+1)δ` each time, (E3)). Hence

```text
‖π(z) - [u(U), v(U)]‖_2 <= K_0 δ,      K_0 = 7 + 2(3|u| + 1) + 2(3|v| + 1).
```

## Step 2. Push into H = G^(L)

Put `V_x = v_x(U)` and `h_x = v_x(φ(ιy) : y ∈ X) ∈ G`.
- **The scalars cancel.** `U_x = c(ιx) ρ(φ(ιx))`, so for any word `w`, `w(U) = κ(w) ρ(w(φι))` with
  `κ(w) = Π_x c(ιx)^(e_x(w))`, where `e_x(w)` is the exponent sum of `x` in `w`.
  - If `L >= 1`, then `v_x ∈ [F(X), F(X)]` has all exponent sums `0`, so `V_x = ρ(h_x)` and `h_x ∈ H`, since evaluating
    a word of `F(X)^(L)` in `G` lands in `G^(L)`.
  - If `L = 0`, then `V_x = U_x = c(ιx) ρ(h_x)` with `h_x = φ(ιx) ∈ G = H`.
  - In both cases `V_x = κ_x ρ(h_x)` with `|κ_x| = 1`, `h_x ∈ H`.
- Let `Ψ : F(X) → H` be the homomorphism `x ↦ h_x`. For every word `w`, `w(V) = κ'(w) ρ(Ψ(w))`, where
  `κ'(w) = Π_x κ_x^(e_x(w))`. For the commutator `[u,v]` all exponent sums vanish, so `[u,v](V) = ρ(Ψ[u,v])`.
- **The push costs O(δ).** `v_x x^(-1) = Π_i g_i r_i^(±1) g_i^(-1)` in `F(X)`, and evaluation at `U` is a homomorphism. By
  unitary invariance of the norm,

```text
‖V_x - U_x‖_2 = ‖(v_x x^(-1))(U) - 1‖_2 <= Σ_i ‖r_i(U) - 1‖_2 <= M_x max_r (3|r| + 2) δ.
```

  So `η := max_x ‖V_x - U_x‖_2 <= K_1 δ`, and `‖w(V) - w(U)‖_2 <= |w| η` for every word `w`.
- **Relators stay nearly scalar.** `ρ(Ψ(r)) = κ'(r)^(-1) r(V)`, so

```text
ε_r := min_{|λ|=1} ‖ρ(Ψ(r)) - λ‖_2 <= ‖r(V) - 1‖_2 <= |r| η + (3|r| + 2) δ <= K_2 δ.
```

- **Head.** `‖ρ(Ψ[u,v]) - [u(U), v(U)]‖_2 = ‖[u,v](V) - [u,v](U)‖_2 <= 2(|u| + |v|) η`. With Step 1,

```text
‖π(z) - 1‖_2 <= (K_0 + 2(|u| + |v|) K_1) δ + ‖ρ(Ψ[u,v]) - 1‖_2.                  (1)
```

## Step 3. Constituent dichotomy

Decompose `ρ|_H = ⊕_σ σ` orthogonally into irreducible representations of `H`, with weights `p_σ = dim σ/N`. For
`h ∈ H`:

```text
‖ρ(h) - 1‖_2² = Σ_σ p_σ ‖σ(h) - 1‖_2²,       min_λ ‖ρ(h) - λ‖_2² >= Σ_σ p_σ min_{λ_σ} ‖σ(h) - λ_σ‖_2².
```

The second holds because a single scalar `λ` is one admissible choice of the `λ_σ`. Each `σ` has exactly one of three types.

- **(i) Every `σ(Ψ(r))`, `r ∈ R`, is a scalar.** Compose `σ∘Ψ : F(X) → U(dim σ)` with the quotient to
  `PU(dim σ)`. It kills `R`. It kills the normal closure of `R`, because a conjugate of a scalar is a scalar. So it
  factors through `Λ = F(X)/<<R>>`, with image in the finite group `σ(H)U(1)/U(1)`. By Step 0 this homomorphism kills
  `μ`, so `σ(Ψ(u))` is a scalar. Hence `σ(Ψ[u,v]) = [σ(Ψ(u)), σ(Ψ(v))] = 1` **exactly**.
- **(ii) Some `r ∈ R` has `|χ̃_σ(Ψ(r))| <= θ`.** Then `min_λ ‖σ(Ψ(r)) - λ‖_2² = 2 - 2|χ̃_σ(Ψ(r))| >= 2(1 - θ)`, so

```text
‖σ(Ψ[u,v]) - 1‖_2² <= 4 <= (2/(1-θ)) Σ_{r∈R} min_λ ‖σ(Ψ(r)) - λ‖_2².
```

- **(iii) Neither.** Every relator has `|χ̃_σ(Ψ(r))| > θ`, and some `σ(Ψ(r))` is not a scalar. This is a template
  constituent, and `‖σ(Ψ[u,v]) - 1‖_2² <= 4`.

Types (i) and (ii) are disjoint, since a scalar has `|χ̃| = 1 > θ`. Summing with weights `p_σ`:

```text
‖ρ(Ψ[u,v]) - 1‖_2² <= (2/(1-θ)) Σ_r ε_r² + 4 p_T(θ, L) <= (2|R|/(1-θ)) K_2² δ² + 4 p_T(θ, L).
```

With `sqrt(A + B) <= sqrt A + sqrt B` and (1), the Theorem holds with

```text
K = K_0 + 2(|u| + |v|) K_1 + sqrt(2|R|/(1-θ)) K_2.                                                    ∎
```

## Step 4. Corollaries

**Corollary 1.** `‖π_k(z) - 1‖_2² = 2 - 2 Re tr π_k(z) → 2 - 2 Re τ(z)` and `def_{F_1}(π_k) → 0`. The Theorem gives
`liminf 2 sqrt(p_T) >= sqrt(2 - 2 Re τ(z))`, that is, `liminf p_T >= (1 - Re τ(z))/2`.

**Corollary 2.** If every irreducible representation of `H = G^(L)` is θ-gapped, then a constituent in which some
relator is not a scalar has `|χ̃_σ| <= θ` at that relator, so it has type (ii). Hence `p_T = 0` and
`‖π(z) - 1‖_2 <= K δ`. For the instances:
- `L = 0`: `constituent-gapped-finite-groups-closed-under-products` (a)–(c) put quotients of `∏ Γ_i × A` (quasi-simple
  classical `Γ_i`, abelian `A`, any number of factors) in `𝒢_{2^(-1/481)}`.
- `L = 4`: for `B = ∏ GL_{N_i}(q_i)`, `B^(j) = ∏ GL_{N_i}(q_i)^(j)`, which for `j >= 4` is the product of the quasi-simple
  `SL_{N_i}(q_i)` over the non-exceptional factors. This is the `L = 4` instance of
  `fp-simple-groups-have-no-models-through-classical-products`, with the standard facts recalled there.
- Extensions: let `B ⊴ G` with `P = G/B` of derived length `<= L'`. Then `B^(L') <= G^(L') <= B`, so
  `B^(L'+4) <= G^(L'+4) <= B^(4)`. Since `B^(4)` is perfect, `B^(L'+4) = B^(4)`, so `G^(L'+4) = B^(4) ∈ 𝒢_θ`.
- Sofic models are the case where `ρ` is a permutation representation.

**Instances of `ι`.** These are as in Step 6 of `jacobson-head-dies-in-gapped-finite-group-models-proof`: the corner
`St_4(J) → EL_n(J)`, `n >= 4`, and `St_4(J) → St_20(L_2(F_2))` via `S ↦ s_2`, `T ↦ t_2`, which sends `x_13(Q)` to
`x_13(s_1 t_1)`.

## Where each hypothesis enters

- **Finite presentation of `St_4(J)`.** It makes `R` finite. That is used in the sum over `r` in Step 3 and in the finite
  words `v_x x^(-1)` of Step 2.
- **Perfectness.** It supplies the words `v_x ∈ F(X)^(L)`. Their zero exponent sums also cancel the scalar cochain.
- **Finite residual.** `μ = x_12(Q)` dies in every finite image. It is used once, in type (i).
- **Commutator shape `z = [μ, ν]`.** In type (i) it turns a scalar into an exact `1`, and it cancels the scalars in Step 2.
- **Not used.** Any gap or rigidity of `G` as a whole, property (T), and any structure of `φ` off `F_1`.

## Calibrations

- `SL_3(Z)` has gapped congruence models and no head from `St_4(J)`: a residually finite target kills `x_12(Q)`.
- In the three-index LEF parabolics of `EL_3(J)` there is no `St_4(J)` source, and the head survives there.
- A single-level truncation model through `GL_d(F_2)` has `H = GL_d(F_2)` simple classical, so `p_T = 0`. This matches
  `jacobson-head-dies-in-gapped-finite-group-models`. The new content is that tensor products and direct sums of such
  models at unboundedly many levels, whose target `∏_k GL_{d_k}(F_2)` is not groupwise rigid, still have `p_T = 0`.
