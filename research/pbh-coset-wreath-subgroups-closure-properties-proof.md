---
rg: 2
id: pbh-coset-wreath-subgroups-closure-properties-proof
kind: route
title: Pull lamps back along the finite cover G/C' -> G/C; realize the centralizer in the monomial embedding G -> L_K wr S_n; realize it diagonally in L_Q x G
target: pbh-coset-wreath-subgroups-closure-properties
requires:
  - pbh-coset-wreaths-iff-identity-edge-hnns
  - type-a-actions-closed-under-products-and-finite-wreaths
  - boone-higman-type-a-class-closed-under-finite-extensions
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

Direct proof (2026-09-18, lane bh-openq-papers). Not independently reviewed.
Conventions:
- `G` acts on the left of coset spaces and on functions by `(g·f)(x) = f(g^(-1)x)`.
- For a group `L` and `n ≥ 1`, `L ≀ S_n = L^n ⋊ S_n`, with `(σ·x)_i = x_(σ^(-1)(i))` and
  `(x, σ)(y, τ) = (x · σ(y), στ)`. This is the convention of
  `type-a-actions-closed-under-products-and-finite-wreaths`, part (b).

**1. Finite-index overgroups inside `G`.**
- Let `π : G/C' → G/C`, `gC' ↦ gC`. It is surjective and `G`-equivariant, with fibres of
  size `[C : C'] < ∞`.
- For `A ∈ B_A`, define `π^* : A^(G/C) → A^(G/C')` by `(π^* f)(x) = f(π(x))`.
  - It is finitely supported, since fibres are finite.
  - It is injective, since `π` is onto, and it is a homomorphism.
  - It is equivariant: `(g·π^* f)(x) = f(π(g^(-1)x)) = f(g^(-1)π(x)) = (π^*(g·f))(x)`.
- So `(f, g) ↦ (π^* f, g)` is an injective homomorphism `A ≀_{G/C} G → A ≀_{G/C'} G`.
- The target is in `B_A` by (b) for `C'`, and `B_A` is closed under subgroups. So (b) holds
  for `C`.

**2. From finite-index subgroups.** Let `n = [G : K]`.
- *Case `C = K`.* `Z/2 ≀_{G/K} G = (Z/2)^n ⋊ G` contains `G ∈ B_A` with index `2^n`. So it
  lies in `B_A` (`boone-higman-type-a-class-closed-under-finite-extensions`), which is (a).
- *Setting.* Otherwise, by (e) for `(K, C)`, pick `L_K ∈ B_A` with `K ≤ L_K` and `m ∈ L_K`
  such that `C = K ∩ C_(L_K)(m)`. Then `m ≠ 1`, since `C ≠ K`.
- *Monomial embedding.*
  - Choose a transversal `t_1 = 1, t_2, …, t_n` with `G = ⊔ t_j K`.
  - For `g ∈ G` write `g t_j = t_(σ_g(j)) κ_j(g)` with `σ_g ∈ S_n` and `κ_j(g) ∈ K`.
  - Put `ι(g) = (x^g, σ_g) ∈ L_K ≀ S_n`, with `x^g_i = κ_(σ_g^(-1)(i))(g)`.
- *`ι` is a homomorphism.* From `gh t_j = t_(σ_gσ_h(j)) κ_(σ_h(j))(g) κ_j(h)` we get
  `σ_(gh) = σ_g σ_h` and `κ_j(gh) = κ_(σ_h(j))(g) κ_j(h)`. Coordinate `i` of `ι(g)ι(h)` is
  `x^g_i x^h_(σ_g^(-1)(i)) = κ_(σ_g^(-1)(i))(g) κ_(σ_h^(-1)σ_g^(-1)(i))(h) = κ_(σ_(gh)^(-1)(i))(gh)`.
- *`ι` is injective.* If `ι(g) = 1` then `σ_g = id` and `κ_1(g) = 1`, so `g = g t_1 = t_1 = 1`.
- *Conjugating the marker.*
  - Let `μ ∈ L_K^n` have `μ_1 = m` and `μ_i = 1` for `i ≠ 1`, and put `m' = (μ, id)`.
  - For `(x, σ)`, `(x,σ)(μ,id)(x,σ)^(-1) = (x·σ(μ)·x^(-1), id)`. Its only nontrivial
    coordinate is `x_(σ(1)) m x_(σ(1))^(-1)`, at `i = σ(1)`.
  - So `ι(g)` commutes with `m'` iff `σ_g(1) = 1` and `x^g_1` commutes with `m`.
  - `σ_g(1) = 1` iff `g ∈ t_1 K = K`. In that case `g t_1 = t_1 g`, so `x^g_1 = κ_1(g) = g`.
  - Hence `C_(ι(G))(m') = ι(K ∩ C_(L_K)(m)) = ι(C)`.
- *The host is in `B_A`.* `L_K ≤ Λ` for some `Λ` with a type (A) action on a set `Y`. By part
  (b) of `type-a-actions-closed-under-products-and-finite-wreaths`, `Λ ≀ S_n` has a type (A)
  action on `Y × {1,…,n}`. So `L_K ≀ S_n ∈ B_A`, and (e) holds for `(G, C)` through `ι`.

**3. Preimages.**
- By (e) for `(Q, C')`, pick `L_Q ∈ B_A` with `Q ≤ L_Q` and `m ∈ L_Q` such that
  `C' = Q ∩ C_(L_Q)(m)`.
- Embed `G` in `L_Q × G` by `g ↦ (φ(g), g)`, which is injective by the second coordinate.
  `L_Q × G ∈ B_A`, as a finite product.
- With `m' = (m, 1)`: `(φ(g), g)` commutes with `m'` iff `φ(g)` commutes with `m`, iff
  `φ(g) ∈ C'`.
- So `C_G(m') = φ^(-1)(C')`, which is (e).
- For `N ⊴ G` with `G/N ∈ B_A`, take `C' = {1}`, which is finite, hence in `CR(G/N)`
  (case 1 of `pbh-coset-wreaths-iff-identity-edge-hnns`). ∎
