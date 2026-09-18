---
rg: 2
id: v-times-sft-gluing-kernel-is-relatively-perfect
kind: claim
title: The doubling swindle holds inside the self-similar gluing group, so its kernel K onto the full group satisfies K = [K, Gamma~]; hence K is central only if it is trivial, and the centrality route to P2'b is equivalent to exactness of the gluing presentation
distinct_from:
  v-times-sft-full-groups-glue-from-two-wreath-pieces: that is the open finite-normal-generation statement P2'b, whose Attempt 1 needs the kernel to be central; this proves the kernel is relatively perfect, so centrality is equivalent to triviality.
  v-times-ample-full-groups-are-generated-by-transpositions: that proves the doubling swindle rho' h rho^-1 = h^(0) h^(1) in the full group; this lifts it to the gluing group, where only the relations of the two pieces and disjoint-cone commutation are available.
  v-times-sft-full-groups-split-into-two-wreath-pieces: that builds the gluing group and its copy endomorphisms; this computes what the copy endomorphisms force on the kernel.
---

**ESTABLISHED** (lane proof, elementary; no priority claimed). Reviewed: gq-referee-a PASS
(`research/artifacts/gq-referee-a-v-times-sft-gluing-kernel-is-relatively-perfect.md`, 59eb5cfa1; nits
N1–N4 applied). The facts used about `D`, the `φ_i` and `[φ_0(Γ~), φ_1(Γ~)] = 1` come from the
unreviewed parent node, but all three follow from (R1) and (R2), which are proved here.

## Setting

Notation is as in `v-times-sft-full-groups-split-into-two-wreath-pieces`:
- `Λ` is finitely generated, `X` is a free subshift, and `Ω = C × X`;
- the two pieces are `M = V(Λ)` and `N_X = LC(X, V) ⋊ Λ`;
- the gluing group is `Γ~ = M *_(V×Λ) N_X / ⟨⟨[M_0, N_1]⟩⟩`, with `π : Γ~ → F(T)` and `K = ker π`;
- `φ_0, φ_1` are the copy endomorphisms, and `D(g) = φ_0(g) φ_1(g)`. `D` is an endomorphism, since
  the two images commute.

Further notation:
- A *product partition* `Q` of `Ω` is a finite partition into pieces `[u] × P`, with `u` a finite
  word and `P ⊆ X` a cylinder.
- For such `Q`, `ρ_Q` is the map `(u a w, x) ↦ (a u w, x)` on each piece `[u] × P`, for digits `a`.
  It lies in `LC(X, V) ≤ N_X`.

## Statement

1. **Swindle in `Γ~`.** Let `g = h_1 ⋯ h_r` with each `h_j ∈ M ∪ N_X`. There are product partitions
   `Q_0, Q_r` with `D(g) = ρ_(Q_0) g ρ_(Q_r)^-1` in `Γ~`. If `g ∈ K`, one may take `Q_0 = Q_r`, so
   `D(k) = ρ k ρ^-1` for some `ρ ∈ N_X`.
2. **Relative perfectness.** `K = [K, Γ~]`.
3. **Centrality is exactness.** `K` is central in `Γ~` iff `K = 1`, iff `π` is an isomorphism.

**Consequence for P2′b.** In Attempt 1 of `v-times-sft-full-groups-glue-from-two-wreath-pieces`
("`K` central plus `H_2(F(T)) = 0`"), the centrality lemma already forces `K = 1`. The `H_2` input
and the retract are then unnecessary. So that route is exactly the claim that the gluing
presentation is exact: `F(T)` is presented by `M`, `N_X` and disjoint-cone commutation. This is the
simple-connectivity form of Attempt 2 (the coset complex), which is shared with bh-g3-steinfarley.

If `K ≠ 1`, then `K` is not central, and `Γ~ → F(T)` is not a central extension.

## Lesson for general BH

In a self-similar presentation with a doubling swindle, the kernel onto the full group is
relatively perfect. So the "central kernel plus acyclic target" trick can only ever prove that the
presentation is exact; it can never split off a nonzero kernel. The swindle that kills the homology
of Thompson-type full groups kills every central quotient of the gluing kernel too.

For every `V × G` full-group host, finite presentation from pieces therefore comes down to exactness
of the local presentation: pieces plus disjoint-cone commutation. That is a Stein--Farley or coset
complex statement, and no homological shortcut exists.

## Proof

**Two relation families available in `Γ~`.**
- *(R1) Disjoint commutation.* `[M_U, N_(U')] = 1` for disjoint nonempty clopen `U, U' ⊆ C`. Here
  `M_U ≤ M` and `N_U = LC(X, V_[U])` are the elements supported in `U × X`. Pick a clopen `A` with
  `U ⊆ A ⊆ C ∖ U'`, and `v ∈ V` with `v(C_0) = A`. Then `v M_0 v^-1 = M_A ⊇ M_U` and
  `v N_1 v^-1 = N_(A^c) ⊇ N_(U')`; conjugate `[M_0, N_1] = 1`. Conjugation by `v` is computed inside
  `M` and inside `N_X`.
- *(R2) Local labels.* For `λ ∈ Λ` and `n ∈ N_U`, `λ|_U n λ|_U^-1 = λ n λ^-1`. Write
  `λ|_U = λ · (λ^-1)|_(U^c)` in `M`, and use (R1) for `(λ^-1)|_(U^c) ∈ M_(U^c)`.

**Item 1, one letter.** Say `h` maps each piece of `Q` onto a piece of `Q'` by
`(u w, x) ↦ (u' w, λ x)`. Then in `F(T)`, `ρ_(Q') h ρ_Q^-1` sends `(a u w, x) ↦ (a u' w, λ x)`,
which is `D(h)`. It remains to see that this identity holds in `Γ~`.
- *Case `h ∈ N_X`.* `Q` refines a table of `h`, and `λ` maps cylinders to cylinders, so
  `Q' = h(Q)` is a product partition. `ρ_Q`, `ρ_(Q')` and `h` lie in `N_X`. For `h = f λ`, the element
  `D(h) = copy_0(f) λ|_(C_0) copy_1(f) λ|_(C_1)` equals `copy_0(f) copy_1(f) λ ∈ N_X`, by (R1) for
  `λ|_(C_0)` against `copy_1(f)`. So the identity is one inside `N_X`, which embeds in `F(T)`.
- *Case `h ∈ M`, `Q` with no dependence on `X`.* Every term lies in `M`, since `ρ_Q ∈ V`. The
  identity holds in `M`, which embeds in `F(T)`.
- *Case `h ∈ M`, general `Q`.*
  - `Q` refines the domain partition `Q^ = {[u_i] × X}` of a table of `h`, and `Q' = h(Q)` refines
    `h(Q^)`. Put `δ_Q = ρ_(Q^)^-1 ρ_Q`. On a piece `[u_i v] × P` it is
    `u_i v a w ↦ u_i a v w`, so `δ_Q = ∏_i δ_i` with `δ_i ∈ N_([u_i])`.
  - The identity reduces to the previous case once `h δ_Q h^-1 = δ_(Q')` holds in `Γ~`.
  - Write `h = ℓ g`, with `g ∈ V` the prefix map `[u_i] → [u'_i]` and `ℓ = ∏_i λ_i|_([u'_i])`. Then
    `g δ_i g^-1 =: ε_i ∈ N_([u'_i])`, computed in `N_X`.
  - The other label factors commute with `ε_i` by (R1). By (R2),
    `λ_i|_([u'_i]) ε_i λ_i|_([u'_i])^-1 = λ_i ε_i λ_i^-1`, which is the piece of `δ_(Q')` over
    `[u'_i]`, computed in `N_X`.

**Item 1, words.** Choose `Q_r` so fine that each `Q_j := (h_(j+1) ⋯ h_r)(Q_r)` refines the table
partition of `h_j`. This is a finite common refinement of pullbacks. Each `Q_j` is a product
partition, because pieces of the form `[u] × P` go to pieces of the same form under elementary maps
`(u w, x) ↦ (u' w, λ x)`. Then `Q_(j−1) = h_j(Q_j)`, and
`D(g) = ∏_j D(h_j) = ∏_j ρ_(Q_(j−1)) h_j ρ_(Q_j)^-1 = ρ_(Q_0) g ρ_(Q_r)^-1`. If `π(g) = 1`, then
`Q_0 = π(g)(Q_r) = Q_r`, piece by piece.

**Item 2.**
- *Copies are conjugate.* Let `σ ∈ V` swap `C_0, C_1` by prefix, and let `v_0, v_1 ∈ V` map `C_0`
  onto `C_00` and onto `C_01` by prefix. On generators, hence on `Γ~`:
  - `σ φ_0(g) σ^-1 = φ_1(g)`;
  - `v_0 φ_0(g) v_0^-1 = φ_00(g)` and `v_1 φ_0(g) v_1^-1 = φ_01(g)`.

  Each is an identity inside `M` for `g ∈ M`. For `g = f λ ∈ N_X`, it holds separately for
  `copy_0(f) ∈ N_X` and for `λ|_(C_0) ∈ M`.
- *The swindle modulo `[K, Γ~]`.* In `Γ~/[K, Γ~]` the image of `K` is central. Let `k ∈ K`, and write
  `x ≡ φ_0(k)`; note `φ_0(K) ⊆ K`.
  - By item 1, `k ≡ ρ k ρ^-1 = φ_0(k) φ_1(k) ≡ x^2`.
  - Applying `φ_0` to item 1 gives `φ_0(ρ) φ_0(k) φ_0(ρ)^-1 = φ_00(k) φ_01(k)`, so `x ≡ x · x`.
  - Hence `x ≡ 1` and `k ≡ 1`. So `K = [K, Γ~]`.

**Item 3.** If `K` is central, then `[K, Γ~] = 1`, and `K = 1` by item 2. `∎`
