---
rg: 2
id: rank-two-affine-wobbling-core-rank-proof
kind: route
title: "The R-core of a finite-index point stabiliser in R² has rank two, since otherwise its stabiliser in Λ is virtually metabelian yet co-amenable; so congruence subgroups dR² die on every orbit, and a faithful action must hide the base on unbounded finite orbits, which a spectral gap forbids by a median cut"
target: rank-two-affine-relative-t-pairs-in-wobbling-groups-fail-tau
requires: []
---

Notation as in the target. The action is written `g·n = ρ(g)n`. The group `Γ` acts on `ℓ²(Y)` for
any `Γ`-set `Y` by `(gf)(y) = f(g^{-1}y)`. Standard facts used without proof:
- abelian groups are amenable;
- an extension of an amenable group by an amenable group is amenable, and so is a group with an
  amenable subgroup of finite index;
- a countable group `G` is amenable iff `ℓ²(G)` has almost invariant vectors (Hulanicki–Reiter).

**Step 0 (item 0: Λ is non-amenable).**
- Suppose `Λ` is amenable. Then `Γ` is amenable, as an extension of `Λ` by the abelian group `A`.
  So `ℓ²(Γ)` has almost invariant vectors.
- By relative (T) it has a nonzero `A`-invariant vector `f`. Then `f(a^{-1}g) = f(g)` for all
  `a ∈ A`, so `f` is constant on each coset `Ag`.
- These cosets are infinite, since `A = R²` and `R` is infinite. A square-summable function
  constant on infinite sets is `0`, which is a contradiction.

**Step 1 (infinite orbits are amenable Γ-sets with finite A-orbits).**
- Let `O` be an infinite `Γ`-orbit and `I_n = O ∩ [−n, n]`. Then `|I_n| → ∞`.
- For `s ∈ S`, a point `y ∈ sI_n \ I_n` has `y = s·z` with `|z| ≤ n < |y|` and `|y − z| ≤ r`. So
  `z` lies in `[−n, −n + r) ∪ (n − r, n]`, a set of at most `2r` integers. Hence `|sI_n \ I_n| ≤ 2r`
  and `|sI_n Δ I_n| ≤ 4r`.
- Put `ξ_n = |I_n|^{-1/2} 1_{I_n} ∈ ℓ²(O)`. Then `‖sξ_n − ξ_n‖² ≤ 4r/|I_n| → 0` for every
  `s ∈ S`, and so for every `g ∈ Γ`, since `‖gh ξ − ξ‖ ≤ ‖hξ − ξ‖ + ‖gξ − ξ‖`. So `ℓ²(O)` has almost
  invariant vectors.
- **(a) Finite `A`-orbits.** Relative (T) gives a nonzero `A`-invariant `f ∈ ℓ²(O)`. It is constant
  on `A`-orbits, so some `A`-orbit in `O` is finite.
  - For `g ∈ Γ` and `x ∈ O`, normality gives `g·(A·x) = A·(g·x)`. So `Γ` permutes the `A`-orbits
    in `O` transitively, and all of them have the same finite size.
  - Hence `A_x` has finite index in `A` for every `x ∈ O`.
- **(b) Invariant mean.** Fix a non-principal ultrafilter `U` on `N`. Then
  `m(φ) = lim_U |I_n|^{-1} Σ_{y∈I_n} φ(y)` is a mean on `ℓ^∞(O)`. It is `s`-invariant for
  `s ∈ S` by the bound `|sI_n Δ I_n| ≤ 4r`, hence `Γ`-invariant.

**Step 2 (co-amenable stabilisers in Λ).**
- Let `O` be any `Γ`-orbit on which `A_x` has finite index for `x ∈ O`. By Step 1 this covers
  every infinite orbit, and it trivially covers every finite orbit.
- Fix `x ∈ O`, put `V = A_x`, and let `K = {λ ∈ Λ : λV = V}`.
- For `g = (λ, a) ∈ Γ` we have `A_{g·x} = g A_x g^{-1} = λ A_x`, because `A` is abelian, so
  conjugation by `a` is trivial on `A`. Hence `Φ: O → {λV : λ ∈ Λ}`, `y ↦ A_y`, is
  `Γ`-equivariant, with `Γ` acting on the target through `π`. The target is `Λ/K`.
- **Claim: `K` is co-amenable in `Λ`.** This means that `Λ/K` carries a `Λ`-invariant mean.
  - If `O` is finite, `Γ_x` has finite index in `Γ`, and `π(Γ_x) ⊆ K` by the formula above. So `K`
    has finite index, and the uniform measure on `Λ/K` is invariant.
  - If `O` is infinite, push the mean `m` of Step 1(b) forward along `Φ`, by
    `m'(ψ) = m(ψ ∘ Φ)`. It is `Λ`-invariant because `Φ` is equivariant and `π` is onto.
- **Claim: if `K` is amenable, so is `Λ`.**
  - Let `m_K` be a left-invariant mean on `K`, and `m'` a `Λ`-invariant mean on `Λ/K`.
  - For `φ ∈ ℓ^∞(Λ)` put `φ̃(λK) = m_K(k ↦ φ(λk))`. This does not depend on the representative:
    replacing `λ` by `λk_0` replaces the function by its translate `k ↦ φ(λk_0 k)`, which has the
    same `m_K`-value.
  - Put `M(φ) = m'(φ̃)`. Then `M` is positive and `M(1) = 1`.
  - For `g ∈ Λ`, the function `φ_g(λ) = φ(gλ)` has `(φ_g)~(λK) = φ̃(gλK)`. So
    `M(φ_g) = m'(φ̃(g·)) = M(φ)`, and `M` is a left-invariant mean on `Λ`.
- By Step 0, **`K` is not amenable.**

**Step 3 (rank lemma).** *Let `V ≤ A` be a subgroup of finite index and `K = {λ ∈ Λ : λV = V}`. Let
`N` be the largest `R`-submodule of `A` contained in `V`, and `W = F·N ⊆ F²` its span. If
`dim_F W ≤ 1`, then `K` is amenable.*
- `N` exists: `{a ∈ A : Ra ⊆ V}` is an `R`-submodule, since `R(a + b) ⊆ Ra + Rb` and
  `R(ca) ⊆ Ra`. It contains every submodule inside `V`.
- `K` permutes the finite set `A/V`. Let `K_0` be the kernel of this action, a finite-index normal
  subgroup of `K`. For `λ ∈ K_0` and `a ∈ A`, `λa − a ∈ V`.
- `(λ − 1)A` is an `R`-submodule of `A`, because `λ` is `R`-linear. It lies in `V`, so
  `(λ − 1)A ⊆ N`. Since `A` spans `F²`, `(λ − 1)F² ⊆ W`.
- If `W = 0`, then `K_0 = {1}`.
- If `W = Fw`, choose `w'` with `(w, w')` a basis of `F²`. For `λ ∈ K_0`, `λw = αw` and
  `λw' = w' + βw` for some `α ∈ F^×` and `β ∈ F`. So in this basis
  `λ = [[α, β], [0, 1]]`.
  - `λ ↦ α` is a homomorphism `K_0 → F^×`.
  - Its kernel consists of matrices `[[1, β], [0, 1]]`, a subgroup of `(F, +)`.
  - So `K_0` is metabelian.
- In both cases `K_0` is amenable, and so is `K`, since `[K : K_0] < ∞`.

**Step 4 (item 1: congruence kernels).**
- Let `O` be a `Γ`-orbit, `x ∈ O`, `V = A_x`. By Step 1(a) for infinite `O`, and trivially for
  finite `O`, `V` has finite index in `A`.
- By Step 2, `K` is not amenable. So by Step 3, `dim_F W = 2`, and `N` contains two `F`-independent
  vectors `n_1, n_2`.
- Let `M ∈ M_2(R)` have columns `n_1, n_2`, and `d_O = det M ≠ 0`. For `a ∈ A`,
  `d_O a = M(adj(M) a)`, and `adj(M) a ∈ R²`. So `d_O a` is an `R`-combination of `n_1, n_2`, and
  `d_O A ⊆ N ⊆ A_x`.
- `d_O A` is `Λ`-invariant, since `λ(d_O A) = d_O λA = d_O A`. For `y = g·x ∈ O` with
  `π(g) = λ`, Step 2 gives `A_y = λA_x ⊇ λ(d_O A) = d_O A`. So `d_O A` fixes `O` pointwise.

**Step 5 (item 2: at most `2r` infinite orbits).**
- The inverse of `ρ(s)` also has displacement at most `r`. So each `Γ`-orbit is connected in the
  Schreier graph whose edges `n — s^{±1}·n` (`s ∈ S`) have length at most `r`.
- Let `O` be unbounded above and `x_0 ∈ O`. For every `n > x_0`, a path in `O` from `x_0` to a
  point `> n + r` has a first vertex `≥ n`. That vertex is within `r` of the previous vertex,
  which is `< n`, so it lies in `[n, n + r)`.
- Distinct orbits are disjoint. So for large `n` at most `r` orbits are unbounded above, and
  likewise at most `r` are unbounded below. An infinite orbit is unbounded on at least one side.
- Put `d = Π d_O` over the infinite orbits, with `d = 1` if there are none. Then `d ≠ 0`, since `R`
  is a domain, and `dA ⊆ d_O A` fixes every infinite orbit pointwise.

**Step 6 (item 3, first part: finite orbits are unbounded).**
- Assume `ρ` is injective, and suppose every finite orbit has at most `M` points.
- For a finite orbit `O`, the kernel `K_O` of `Γ → Sym(O)` is normal of index at most `M!`. It is
  the kernel of a homomorphism `Γ → S_k` with `k ≤ M`. Such a homomorphism is determined by the
  images of the finitely many elements of `S`. So the `K_O` take finitely many values, and
  `A' = A ∩ ⋂_{O finite} K_O` has finite index in `A`.
- Take `d` from Step 5. Multiplication by `d` is injective on `A`, since `R` is a domain, so `dA`
  is infinite. Then `dA ∩ A'` has finite index in `dA`, so it contains some `a ≠ 0`.
- This `a` fixes every infinite orbit pointwise by Step 5, and every finite orbit pointwise because
  `a ∈ A'`. So `ρ(a) = 1`, contradicting injectivity.

**Step 7 (two spectral lemmas).**
- **(7a) Median cut.** *Let `Q' ⊂ Γ` be finite, `r' = max_{q∈Q'} sup_n |q·n − n|`, and `O` a finite
  orbit with `m = |O| ≥ 2`. If the gap of `Q'` on `O` is at least `κ > 0`, then `m ≤ 16r'/κ²`.*
  - List `O` as `x_1 < ⋯ < x_m`. Let `B = {x_1, …, x_k}` with `k = ⌊m/2⌋`, and
    `f = (m − k)1_B − k 1_{O\B}`. Then `Σ f = 0` and `‖f‖² = k(m − k)m ≥ m³/8`, using
    `k(m − k) ≥ m²/8` for `m ≥ 2`.
  - A point `z ∈ B` with `q·z ∉ B` satisfies `x_k < q·z ≤ z + r'`, so `z ∈ (x_k − r', x_k]`. There
    are at most `r'` such `z`. So `|qB \ B| ≤ r'` and `|qB Δ B| ≤ 2r'`.
  - `qf − f` vanishes off `qB Δ B` and has absolute value `m` on it. So `‖qf − f‖² ≤ 2r'm²`.
  - The gap gives `κ² m³/8 ≤ 2r'm²`, that is `m ≤ 16r'/κ²`.
- **(7b) Gap transfer through relative (T).** *There are a finite `Q_T ⊂ Γ` and `ε > 0` with the
  following property. Let `Q ⊂ Λ` be finite with lifts `Q̃ ⊂ Γ`. If the gap of `Q` on the `Λ`-set
  `O/A` is at least `κ' > 0` for a finite orbit `O`, then the gap of `Q̃ ∪ Q_T` on `O` is at
  least `min(κ', ε)/√2`.*
  - For a finite orbit `O`, let `P_O` be the orthogonal projection of `ℓ²_0(O)` onto its
    `A`-invariant vectors. Since `A` is normal, the `A`-invariant subspace is `Γ`-invariant, so
    `P_O` commutes with `Γ`.
  - The representation `σ = ⊕_{O finite} (1 − P_O)ℓ²_0(O)` has no nonzero `A`-invariant vector. So
    by relative (T) it has no almost invariant vectors. That is, there are finite `Q_T` and
    `ε > 0` with `max_{g∈Q_T} ‖gη − η‖ ≥ ε‖η‖` for every `η` in `σ`, in particular for every
    `η ∈ (1 − P_O)ℓ²_0(O)`.
  - All `A`-orbits in `O` have the same size `c`, since `Γ` permutes them transitively. So
    `u ↦ c^{-1/2} (u ∘ quotient map)` is a unitary isomorphism `ℓ²_0(O/A) → P_O ℓ²_0(O)`. It
    intertwines the `Λ`-action with the `Γ`-action, `Γ` acting through `π`.
  - For `f ∈ ℓ²_0(O)`, write `f = P_O f + (1 − P_O) f`. For every `g ∈ Γ`, both parts move
    orthogonally:
    `‖gf − f‖² = ‖gP_O f − P_O f‖² + ‖g(1 − P_O)f − (1 − P_O)f‖²`.
  - The maximum over `Q̃` of the first term is at least `κ'²‖P_O f‖²`. The maximum over `Q_T` of the
    second is at least `ε²‖(1 − P_O)f‖²`. The larger of the two is at least half their sum, so
    `max_{g∈Q̃∪Q_T} ‖gf − f‖² ≥ min(κ', ε)² ‖f‖²/2`.

**Step 8 (item 4 and the second part of item 3).**
- Assume `ρ` is injective. Suppose some finite `Q ⊂ Λ` has gap at least `κ' > 0` on `O/A` for every
  finite orbit `O`.
- By (7b), `Q' = Q̃ ∪ Q_T` has gap at least `κ = min(κ', ε)/√2` on every finite orbit. By (7a),
  every finite orbit has at most `max(1, 16r'/κ²)` points. This contradicts Step 6. So the
  infimum in item 4 is `0`.
- Taking `Q = π(S)` shows that `Λ` fails (τ). If `Γ` had (τ), some finite generating set of `Γ`
  would have a uniform gap on all finite orbits, and (7a) together with Step 6 would give the same
  contradiction. So `Γ` fails (τ).
- Suppose `|O/A| ≤ C` for every finite orbit `O`. A transitive `Λ`-set with at most `C` points is
  determined up to isomorphism by the images of the finitely many elements of `π(S)` in `S_k`,
  `k ≤ C`, so there are finitely many of them.
  - On each, `π(S)` has positive gap. `ℓ²_0` is finite-dimensional and, by transitivity, contains
    no nonzero `Λ`-invariant vector, so `f ↦ max_{s} ‖sf − f‖` is bounded below on its unit
    sphere.
  - The minimum of these finitely many gaps is a uniform `κ' > 0`, which contradicts the previous
    bullet. So `|O/A|` is unbounded.

**Step 9 (item 5).**
- If `Λ` has (τ), some finite generating set `Q` of `Λ` has a uniform gap on all finite transitive
  `Λ`-sets, in particular on the `O/A`. By Step 8 no injective `ρ` exists. Any faithful action of a
  group containing `Γ` restricts to a faithful action of `Γ`, so such a group is not in `W(Z)`
  either.
- **Passing to `[[X]]`.**
  - Let `x*` have a dense `σ`-orbit, which is infinite, and identify `Z` with it by `j ↦ σ^j x*`.
  - Each `f ∈ [[X]]` has a continuous cocycle `k_f` with `f(y) = σ^{k_f(y)} y`. It is bounded on
    the compact space `X`, so `f` acts on the orbit by a bounded-displacement bijection.
  - An `f` acting trivially is the identity on a dense set, hence everywhere by continuity. So this
    is an injective homomorphism `[[X]] → W(Z)`, and a copy of `Γ` in `[[X]]` would give one in
    `W(Z)`.
