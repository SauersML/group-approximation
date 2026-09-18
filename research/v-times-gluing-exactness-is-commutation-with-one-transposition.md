---
rg: 2
id: v-times-gluing-exactness-is-commutation-with-one-transposition
kind: claim
title: The gluing group of V times any Lambda-space is the normal closure of one Thompson transposition, so its kernel onto the full group is trivial iff it commutes with that transposition, and finitely normally generated iff finitely many kernel relators force that commutation
requires:
  - v-times-sft-gluing-kernel-is-relatively-perfect
  - v-times-sft-full-groups-split-into-two-wreath-pieces
distinct_from:
  v-times-sft-gluing-kernel-is-relatively-perfect: that proves K = [K, Gamma~], so a central kernel is trivial; this proves Gamma~ is the normal closure of any one nontrivial element of V, so a kernel that commutes with ONE transposition is already central, and it states the finite-normal-generation form.
  v-times-full-groups-have-local-transposition-presentations: that proposes an infinite Quick-type presentation of F(T) by all basic transpositions and needs every conjugacy relation lifted; this shows exactness needs only that lifting one fixed transposition tau_0 around every relator loop returns tau_0.
  gluing-kernels-descend-from-the-full-shift: that reduces P2'b over an alphabet to the full shift, FSG(Lambda, A); this restates FSG as a commutation statement about one element and records the tested routes to it.
---

**ESTABLISHED** (lane proof, elementary; unreviewed; no priority claimed). bh-p2b-exact, 2026-09-18.
It addresses gate 5 of the v5 synthesis (P2′b) and the statement FSG(Λ, A). **FSG(Z, 2) itself stays OPEN.**

## Setting

- Notation as in `v-times-sft-gluing-kernel-is-relatively-perfect`: `Γ~ = M *_(V×Λ) N_X / ⟨⟨[M_0, N_1]⟩⟩`,
  `π : Γ~ → F(T)` and `K = ker π`, with `M = C(C, Λ) ⋊ V`, `N_X = LC(X, V) ⋊ Λ` and `T = G_V × (Λ ⋉ X)`.
- `X` is any compact totally disconnected Λ-space. The full shift `A^Λ` is included.
  - The relatively-perfect node is stated for free subshifts. Its proof uses only (R1), (R2), the swindle on
    product partitions and the conjugacy of copies, and none of these uses freeness.
  - So `K = [K, Γ~]` holds for every `X`.
- `τ_0 = (00 01) ∈ V` swaps the cones `C_00` and `C_01` by prefix. `V ≤ M ∩ N_X` embeds in `Γ~`.

## Statement

1. **One transposition normally generates.** `⟨⟨v_0⟩⟩_(Γ~) = Γ~` for every `v_0 ∈ V ∖ {1}`.
2. **Commutation criterion.** Let `R ⊴ Γ~` with `R ⊆ K`, and let `v_0 ∈ V ∖ {1}`. Then `K = R` iff
   `[K, v_0] ⊆ R`. In particular:
   - `K = 1` iff every kernel element commutes with `v_0`;
   - `K = ⟨⟨[k, v_0] : k ∈ K⟩⟩`.
3. **FSG as a commutation statement.** `K` is finitely normally generated iff there is a finite set `R ⊆ K`
   such that, in `Γ~/⟨⟨R⟩⟩`, every kernel element commutes with `τ_0`. By
   `gluing-kernels-descend-from-the-full-shift`, FSG(Λ, A) is this statement for `X = A^Λ`.
4. **Centralizers of `τ_0` lift.** `π(C_(Γ~)(τ_0)) = C_(F(T))(τ_0)`.

## Monodromy form (a restatement of 2, for word-level proofs)

Let `k = h_1 ⋯ h_r ∈ K`, with each `h_j ∈ M ∪ N_X`. Put `τ^(j) = (h_j ⋯ h_r) τ_0 (h_j ⋯ h_r)^(-1)` for
`1 ≤ j ≤ r`, and `τ^(r+1) = τ_0`.
- Each `τ^(j)` is a lift of the transposition `π(h_j ⋯ h_r) τ_0 π(h_j ⋯ h_r)^(-1)`.
- `τ^(j) = h_j τ^(j+1) h_j^(-1)`. This step is computed inside `M` or inside `N_X` whenever `τ^(j+1)` lies in
  the same piece as `h_j`.
- Item 2 says the gluing presentation is exact iff **lifting τ_0 around every relator loop returns τ_0**.

A Quick-type local presentation (`v-times-full-groups-have-local-transposition-presentations`) is one way to
prove this: its conjugacy relations (C) make the one-step lifts path-independent. Item 2 shows that only the
orbit of the single transposition `τ_0` matters, and item 3 says the same for finite normal generation.

## Routes to FSG(Z, 2) tested here

- **Bounded factorization is dead.**
  - Suppose `Γ~ = M N_X M` as sets. Then `K = 1`: if `m' n m ∈ K`, then `π(n) ∈ π(N_X) ∩ π(M) = V × Λ`, and
    `π` is injective on `M` and on `N_X`.
  - But already `F(T) ≠ M N M` for `(Λ, A) = (Z, 2)`. For `g = m' n m`, the Z-label of `g` at `(c, x)` is
    `f(c) + φ(g_C(c, x))` for some locally constant `f, φ : C → Z`, where `g_C` is the `C`-coordinate of `g`.
  - Let `t_1` swap `C_00 × Q` and `C_01 × σQ` by `(00w, x) ↦ (01w, σx)`, with `Q = {x(0) = 1}`. Let
    `t_2 = (00 01)^[Q']`, with `Q'` a nonempty cylinder disjoint from `Q ∪ σQ`. Then `t_1 t_2` sends `00w` to
    `01w` with label 1 over `Q` and with label 0 over `Q'`. That would force `f(00w) + φ(01w) = 1 = 0`.
- **Centralizer lifting (item 4) holds but is not enough.** It gives `π^(-1)(C(τ_0)) = C_(Γ~)(τ_0) · K`, which
  is item 2 read backwards.
- **Complexity induction (OPEN, the proposed Quick-type route).** This concerns the conjugacy relations of
  lifts with overlapping supports.
  - The sets of cylinder windows are invariant under Γ~, since `M` and `N` move `X` only by global
    translations. So overlapping configurations with windows of unbounded complexity form infinitely many
    Γ~-orbits, and Quick's finite-orbit step cannot apply verbatim.
  - They could still follow from site-cylinder configurations. In `N`, `[a, b]^[P_1 ∩ P_2] = [a^[P_1], b^[P_2]]`,
    so a relation for a transposition conditioned on `P_1 ∩ P_2` follows from the relations for `P_1` and
    `P_2` by conjugating commutators.
  - After cone sliding (`v-cone-sliding-localizes-disjoint-support-relations`), the site-cylinder base cases
    lie in finitely many orbits.
  - The missing lemma is **multiplicativity**: the piecewise lift of `m τ m^(-1)` (`m ∈ M`, `τ` a
    conditioned transposition) must equal the commutator of the lifts of its lower-complexity factors. That is
    the one place where a proof of FSG(Z, 2) must do work.

## Lesson for general BH

In Thompson-type self-similar models, **the kernel onto the full group is controlled by one element**:
- the model is the normal closure of any nontrivial Thompson element, by simplicity of V and the label
  swindle;
- the kernel is relatively perfect.

So a kernel element that commutes with one transposition `τ_0` is central, hence trivial. Exactness of any
gluing presentation `M *_(V×Λ) N / ⟨⟨disjoint-cone commutation⟩⟩` is therefore a **monodromy statement**:
lifting `τ_0` along relator loops has trivial holonomy. Finite normal generation says the holonomy is generated
by finitely many loops.

This transfers verbatim to every `G_V × H` host: Brin–Thompson, 𝒯_m, and the operad and cube-category hosts.
The work always sits in one multiplicativity lemma for conjugating conditioned transpositions by labels,
never in homology.

## Proof

**Item 1.** Since `V` is simple (Higman), the normal closure of `v_0` in `V` is `V`. So it suffices to show
`⟨⟨V⟩⟩ = Γ~`. As `Γ~ = ⟨M, N_X⟩`, it is enough to show that both lie in `⟨⟨V⟩⟩`.
- **`M`.** Work in `M/⟨⟨V⟩⟩_M`, where `f ≡ v f v^(-1) = f ∘ v^(-1)`.
  - Every `f ∈ C(C, Λ)` is a product of commuting elements `λ|_U` over a partition of `C` into proper cones
    (split `C = C_0 ⊔ C_1` if needed).
  - For a proper cone `[u]`, choose `v ∈ V` mapping `[u0]` onto `[u]` by a prefix map. Then
    `v λ|_([u0]) v^(-1) = λ|_([u])`, so `λ|_([u]) ≡ λ|_([u0])`. In the same way `λ|_([u]) ≡ λ|_([u1])`.
  - Then `λ|_([u]) = λ|_([u0]) λ|_([u1]) ≡ λ|_([u])^2`, so `λ|_([u]) ≡ 1`.
- **`N_X`.** `Λ ≤ M`, via `V × Λ`. For clopen `P ⊆ X` and `a, b ∈ V`, compute pointwise in `N_X` to get
  `[a^[P], b] = [a, b]^[P]`. `V` is perfect and `a ↦ a^[P]` is a homomorphism, so every `v^[P]` lies in
  `⟨⟨V⟩⟩`. Every element of `LC(X, V)` is a product of such `v^[P]` over a clopen partition.

**Item 2.**
- *If.* Let `[K, v_0] ⊆ R`, and put `Γ̄ = Γ~/R`, with `K̄` the image of `K`. Let `k̄ ∈ K̄` and `g ∈ Γ̄`. Then
  `[k̄, g v̄_0 g^(-1)] = g [g^(-1) k̄ g, v̄_0] g^(-1) = 1`, since `K̄` is normal. So `K̄` centralizes
  `⟨⟨v̄_0⟩⟩ = Γ̄` (item 1), and `K̄` is central.
- By `v-times-sft-gluing-kernel-is-relatively-perfect`, `K = [K, Γ~]`, so `K̄ = [K̄, Γ̄] = 1`, and `K ⊆ R`.
- *Only if.* This is immediate, since `[K, v_0] ⊆ K = R`.
- For the last clause, apply the criterion with `R = ⟨⟨[k, v_0] : k ∈ K⟩⟩`.

**Item 3.** Apply item 2 with `R` replaced by `⟨⟨R⟩⟩` and `v_0 = τ_0`.

**Item 4.** Let `g ∈ C_(F(T))(τ_0)`.
- **Splitting.** `g` preserves `Fix(τ_0) = C_1 × X`, and hence `C_0 × X`. So `g = g_1 ⊔ g_0`.
- **The part `g_1`.** It is supported in `C_1 × X`, so `g_1 = copy_1(h)` with `h ∈ F(T)`. Since `π` is onto,
  `g_1 = π(φ_1(y))` for some `y`.
  - `φ_1(Γ~)` commutes with `φ_0(Γ~)` (split node, item 5).
  - `τ_0 = φ_0(σ)`, where `σ = (0 1) ∈ V`.
  - So `φ_1(y) ∈ C_(Γ~)(τ_0)`.
- **The part `g_0`.** It commutes with the swap `00w ↔ 01w`. So it induces a homeomorphism `h` of the orbit
  space `C_00 × X`, given locally by `T`-germs, together with a locally constant `c : C_00 × X → Z/2`.
  - `g_0 = s_E ∘ (h ⊔ τ_0 h τ_0)`, where `s_E` swaps `p ↔ τ_0 p` over a clopen `E ⊆ C_00 × X`.
- **The factor `s_E`.** `E` is a finite union of pieces `[00u] × P`, so `s_E = ∏ (00u 01u)^[P] ∈ LC(X, V) ≤ N_X`.
  It commutes with `τ_0 ∈ N_X` in `F(T)`, hence in `N_X ≤ Γ~`, because `N_X → F(T)` is the inclusion.
- **The diagonal factor.** Write `h = copy_00(h')` and `h' = π(y')`. Then `h ⊔ τ_0 h τ_0 = π(φ_0(D(y')))`, where
  `D(y') = φ_0(y') φ_1(y')`.
  - By item 2 of the relatively-perfect node, `σ φ_0(y') σ^(-1) = φ_1(y')`. Since `σ^2 = 1`, also
    `σ φ_1(y') σ^(-1) = φ_0(y')`.
  - The two copies commute, so `σ D(y') σ^(-1) = D(y')`. Applying `φ_0`, the element `φ_0(D(y'))` commutes
    with `τ_0`.

So `g` is the image of a product of elements of `C_(Γ~)(τ_0)`. The inclusion
`π(C_(Γ~)(τ_0)) ⊆ C_(F(T))(τ_0)` is clear. ∎

## Referee (bh-ref-ffwz, 2026-09-18): PASS for items 1–2 (items 3–4 read, not needed for K = 1)

- **Item 1.**
  - The label swindle `λ|_[u] ≡ λ|_[u0] ≡ λ|_[u1]` gives `λ|_[u] ≡ λ|_[u]^2 ≡ 1` in
    `M/⟨⟨V⟩⟩`.
  - `[a^[P], b] = [a,b]^[P]` holds pointwise, and `V` is perfect. So `N_X ⊆ ⟨⟨V⟩⟩`.
  - Simplicity of `V` (Higman) finishes.
- **Item 2.**
  - If `[K, v_0] ⊆ R`, then `K̄` centralizes `⟨⟨v̄_0⟩⟩ = Γ̄`.
  - Relative perfectness (`v-times-sft-gluing-kernel-is-relatively-perfect`, referee-a PASS)
    then kills it.
  - That node is stated for free subshifts and finitely generated `Λ`. I checked that neither
    hypothesis is used: tables and product partitions only need clopen `P` and `λ` mapping
    clopens to clopens.
- **Items 3–4.** They are correct as far as read. Item 4 is not used by
  `v-times-gluing-presentations-are-exact`.
- The monodromy form is a faithful restatement of item 2.
