---
rg: 2
id: relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two-proof
kind: route
title: Swap the base by an adjunction along a homotopy equivalence, glue copies along the base, and slice a 2-dimensional K(Gamma_aleph_1,1) by a countable elementary submodel and pass to the cover for one copy of G
target: relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two
requires:
  - continuous-free-chain-unions-have-gd-two
---

All complexes are CW complexes. Maps between them are cellular and based at a vertex. `Γ_κ = Γ_κ(H,G)`, and `ι_ξ: G → G_ξ ≤ Γ_κ` is the `ξ`-th copy, which is the identity on `H`. For `S ⊆ κ`, `Γ_S = ⟨G_ξ : ξ ∈ S⟩`.

## Standard facts used

- **(F1) Amalgams** (Serre, *Trees*, I.1 and I.4; normal form theorem).
  - Each `ι_ξ` is injective, and `Γ_S ≅ ⁎_H {G_ξ : ξ ∈ S}`.
  - `Γ_κ ≅ Γ_S *_H Γ_{κ∖S}`.
  - In any amalgam `A *_C B` one has `A ∩ B = C`. Hence for `η ∉ S`, `Γ_S ∩ G_η = H` (apply this to `Γ_S` and `Γ_{κ∖S} ⊇ G_η`).
- **(F2) Subcomplexes.** Let `Y ⊆ X` be connected 2-dimensional complexes, `X` aspherical, and `π_1 Y → π_1 X` injective. Then `Y` is aspherical.
  - The component of `p^{-1}(Y)` in the universal cover `X̃` is simply connected, so it is the universal cover of `Y`.
  - It is a 2-dimensional subcomplex of the contractible 2-complex `X̃`. With no 3-cells, `H_2` of a subcomplex is a subgroup of `H_2(X̃) = 0`.
  - By Hurewicz and Whitehead it is contractible.
- **(F3) Covers of subcomplexes.** Let `Y ⊆ X` be `π_1`-injective with image `A ≤ B = π_1 X`, and let `q: X̂ → X` be the cover corresponding to `C ≤ B`, with base lift `x̂_0`.
  - The component `Ŷ` of `q^{-1}(Y)` through `x̂_0` is a subcomplex of `X̂`.
  - `Ŷ → Y` is the cover corresponding to `A ∩ C`: a loop in `Y` lifts to a closed loop exactly when its class lies in `C`.
  - `π_1(Ŷ) = A ∩ C → π_1(X̂) = C` is the inclusion. It is injective, because the composite to `π_1 X` is.
- **(F4) Gluing theorem** (R. Brown, *Topology and Groupoids*, 7.5.7, cited from memory). If `i: A → X` is a cofibration and `f: A → B` is a homotopy equivalence, then the induced map `X → X ∪_f B` is a homotopy equivalence.
  - If `(X, A)` is a CW pair and `f` is cellular, then `X ∪_f B` is a CW complex. It has `B` as a subcomplex, and its other cells are the cells of `X ∖ A`.
- **(F5) Whitehead's gluing theorem** (J.H.C. Whitehead, Fund. Math. 32 (1939); Scott–Wall 1979, Prop. 3.6). Let `Z = A ∪ B` with `A`, `B`, `A ∩ B` connected aspherical subcomplexes, and suppose `π_1(A∩B)` injects into both `π_1 A` and `π_1 B`. Then `Z` is aspherical and `π_1 Z = π_1 A *_{π_1(A∩B)} π_1 B`.
- **(F6) Directed unions** (Lemma 3 of `continuous-free-chain-unions-have-gd-two-proof`, whose proof uses only compactness and so applies verbatim to directed unions). A directed union of aspherical subcomplexes is aspherical, with `π_1` the colimit.

## (a) ⇒ (b): the swap lemma

Let `K' ⊆ X'` witness `RP(H,G)`. In particular `K'` is a 2-dimensional `K(H,1)`, so one exists. Let `K` be any 2-dimensional `K(H,1)` with a given identification `π_1 K ≅ H`.

1. **The map `g`.** Since `K` is a `K(H,1)`, there is a based map `g: K' → K` inducing the identity of `H`. By cellular approximation it can be taken cellular. It is a `π_1`-isomorphism of aspherical complexes, hence a homotopy equivalence (Whitehead).
2. **The complex.** Put `X = X' ∪_g K`. By (F4):
   - `X` is a 2-dimensional CW complex containing `K` as a subcomplex;
   - the map `ĝ: X' → X` is a homotopy equivalence, so `X` is a `K(G,1)`.
3. **Fundamental group.** The square `j ∘ g = ĝ ∘ i` commutes, with `i: K' ↪ X'` and `j: K ↪ X`. So `j_* = ĝ_* ∘ i_* ∘ g_*^{-1}`. Identifying `π_1 X` with `G` via `ĝ_*`, `j_*` is the inclusion `H ≤ G`. ∎

Conversely (b) ⇒ (a) is trivial.

## (b) ⇒ (d): gluing copies

Let `K ⊆ X` be as in (b). Let `Z_κ` be `κ` copies `X_ξ` of `X` glued along the common subcomplex `K`.
- **Finite stages.** For finite `S ⊆ κ`, the sub-star `Z_S` is built by successive adjunction along `K`. (F5) applies at each step, with `A = Z_{S'}` and `B = X_ξ`: `π_1 K = H` injects into `G` and into `Γ_{S'}` by (F1). So `Z_S` is aspherical with `π_1 = Γ_S`.
- **All of `κ`.** `Z_κ` is the directed union of the `Z_S` over finite `S`. By (F6) it is a 2-dimensional `K(Γ_κ,1)`. ∎

(d) ⇒ (c) is trivial.

## (c) ⇒ (a): slicing an uncountable amalgam

If `G = H`, take `X = K` for any 2-dimensional `K(H,1)`. One exists, because `H = G_0 ≤ Γ_{ℵ_1}` and a cover of a 2-dimensional `K(Γ_{ℵ_1},1)` gives one. So assume `G ≠ H`.

**Setup.**
- Let `X` be a 2-dimensional `K(Γ,1)` with `Γ = Γ_{ℵ_1}`, a base vertex `x_0`, and an isomorphism `φ: π_1(X,x_0) → Γ`.
- Fix a regular `θ` with `X, Γ, (ι_ξ)_{ξ<ω_1}, φ ∈ H(θ)`.
- Let `M ≺ H(θ)` be countable and contain `X, x_0, Γ, G, H, (ι_ξ)_ξ, φ`.

**Standard facts about `M`.**
- **(E1)** Every finite set or finite tuple that belongs to `M` has all its entries in `M`.
- **(E2)** Every first-order statement with parameters in `M` that is true in `H(θ)` has a witness in `M`.
- **Countable members are subsets.** A countable `A ∈ M` satisfies `A ⊆ M`: there is a surjection `ω → A` in `M`, and `ω ⊆ M`. In particular `G ⊆ M`.
- **`M ∩ ω_1` is an ordinal.** `δ := M ∩ ω_1` is a countable ordinal with `δ ≥ ω`.

**Step 1: `X_M`, the union of the cells of `X` that belong to `M`, is a subcomplex.**
- For a cell `e ∈ M`, the smallest finite subcomplex containing `e` is definable from `X` and `e`. So it belongs to `M`, and all its cells belong to `M` by (E1).

**Step 2: `φ` maps the image of `π_1(X_M,x_0)` onto `Γ ∩ M`.**
- **Into.** Every class in `π_1(X_M,x_0)` is represented by an edge loop in `X_M`. That loop is a finite tuple of cells in `M`, hence belongs to `M`, so its `φ`-value belongs to `M`.
- **Onto.** For `γ ∈ Γ ∩ M`, "some edge loop at `x_0` has `φ`-value `γ`" is true, so by (E2) there is such a loop in `M`. Its edges lie in `M` by (E1), so the loop lies in `X_M`.

**Step 3: `X_M ↪ X` is `π_1`-injective.**
- Let `w` be an edge loop in `X_M` that is null-homotopic in `X`. By compactness, "there is a finite subcomplex `L ⊆ X` containing `w` in which `w` is null-homotopic" is true.
- The parameters `X` and `w` lie in `M`, so by (E2) such an `L` lies in `M`. By (E1) all its cells lie in `M`, so `L ⊆ X_M` and `w` is null-homotopic in `X_M`.
- By (F2), `X_M` is aspherical.

**Step 4: `Γ ∩ M = Γ_δ`.**
- **`⊇`.** For `ξ < δ` and `g ∈ G`, the parameters `ξ`, `g` and `(ι_ξ)` lie in `M`, so `ι_ξ(g) ∈ M`.
- **`⊆`.** For `γ ∈ Γ ∩ M`, the statement "`γ = ι_{ξ_1}(g_1) ⋯ ι_{ξ_n}(g_n)` for some finite tuple" is true. So by (E2) it has a witness tuple in `M`, and then `ξ_i ∈ M ∩ ω_1 = δ`.

**Step 5: pass to the cover for one copy of `G`.**
- Let `q: X̂ → X` be the covering corresponding to `G_δ = ι_δ(G)`. It is a 2-dimensional `K(G_δ,1)`.
- By Steps 3 and 4, `X_M` is `π_1`-injective with image `Γ_δ`. By (F3), the component `Ŷ` of `q^{-1}(X_M)` through the base lift is a subcomplex of `X̂`, with `π_1 Ŷ = Γ_δ ∩ G_δ` mapping injectively to `π_1 X̂ = G_δ`.
- `δ ∉ δ`, so (F1) gives `Γ_δ ∩ G_δ = H`.
- `Ŷ` covers the aspherical `X_M`, so it is aspherical.
- Transporting along `ι_δ: G → G_δ`, which is the identity on `H`, `Ŷ ⊆ X̂` witnesses `RP(H,G)`. ∎

## The cd bound

Assume `cd G ≤ 2` and `pd_{ZG} I_{G/H} ≤ 1`. Fix a cardinal `κ ≥ 1`.

1. **Restriction is onto.** Apply `Ext_{ZG}(−,M)` to `0 → I_{G/H} → Z[G/H] → Z → 0` and use Shapiro. This gives an exact sequence `H^2(G,M) −res→ H^2(H,M) → Ext^2_{ZG}(I_{G/H},M)`, and the last term is `0`. So `res^G_H: H^2(G,M) → H^2(H,M)` is onto for every `ZG`-module `M`.
2. **The Bass–Serre tree.**
   - `Γ_κ` is the fundamental group of the tree of groups with a central vertex `v_*` carrying `H`, leaves `v_ξ` carrying `G`, and edges `e_ξ = (v_*, v_ξ)` carrying `H`. Its Bass–Serre tree `T` has cellular chain complex `0 → ⊕_ξ Z[Γ_κ/H] −∂→ Z[Γ_κ/H] ⊕ ⊕_ξ Z[Γ_κ/G_ξ] → Z → 0`, with `∂ e_ξ = v_ξ − v_*`.
   - Apply `Ext_{ZΓ_κ}(−,M)` together with Shapiro's lemma (Brown, *Cohomology of Groups*, VII.9). This gives the exact sequence `H^2(H,M) × ∏_ξ H^2(G_ξ,M) −δ→ ∏_ξ H^2(H,M) → H^3(Γ_κ,M) → H^3(H,M) × ∏_ξ H^3(G_ξ,M) = 0`, where `δ(x,(y_ξ)) = (res y_ξ − x)_ξ`.
3. **Conclusion.** By step 1, applied to each `G_ξ ≅ G`, `δ` is onto. So `H^3(Γ_κ,M) = 0` for all `M`, and the higher terms vanish in the same way. Hence `cd Γ_κ ≤ 2`. ∎

## Calibration

- **Free `H`.** Lemma 1 of `continuous-free-chain-unions-have-gd-two-proof` gives (b). Then (d) says `⁎_H G` over any number of copies has `gd ≤ 2`, which matches Lemma 2 there (a tree of groups with free edge groups and `gd ≤ 2` vertex groups).
- **Klein bottle (a failing pair).** Let `H = Z^2 ≤ G = π_1(Klein bottle)`, with `G/H` of order 2.
  - (a) fails, because the pd condition fails (see `relative-countable-eg-gives-eg-for-aleph-one-groups`). So the equivalence predicts `gd Γ_{ℵ_1} > 2`, and indeed `cd Γ_2 = 3`.
  - To see this, let `k: Γ_2 → Z/2 × Z/2` send `G_1` and `G_2` onto the two factors through `G → G/H`; it kills `H`. The kernel of `k` acts on the Bass–Serre tree with vertex and edge stabilizers the conjugates of `H`, so the quotient graph of groups has every group equal to `Z^2`.
  - The quotient graph has 2 + 2 vertices and 4 edges, so it is a circle. With all edge maps isomorphisms, `ker k ≅ Z^2 ⋊ Z`, which has `cd 3`.
  - `Γ_2 ≤ Γ_{ℵ_1}`, so `gd Γ_{ℵ_1} ≥ 3`, as predicted.
- **The `H = 1` case.** `Γ_κ(1,G)` is a free product of copies of `G`, and (a) ⇔ (c) reduces to `gd G ≤ 2 ⇔ gd (⁎^{ω_1} G) ≤ 2`, which is standard.
