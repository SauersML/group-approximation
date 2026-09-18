---
rg: 2
id: normalized-benign-witnesses-give-the-semidirect-join-proof
kind: route
title: "Proof: a normalizing H makes Sigma H a subgroup meeting K in LH; lifts to the normalizer straighten Weyl embeddings; Goursat and Higman's universal group reduce (d) to one fibre product; the double turns r.e. subgroups into equalizers"
target: normalized-benign-witnesses-give-the-semidirect-join
requires:
  - two-occurrence-realizability-is-type-f-benignness
  - type-f-normal-closure-lemma-is-the-whole-benign-problem
---

Verification tier: proposed-established. Elementary, on top of the finiteness
facts (P), (A), (E) and the closure properties (preimages along homomorphisms
of type `F_m` groups, intersections, injective images) of
`two-occurrence-realizability-is-type-f-benignness` (Step 4 of its proof).

## Step 1. Item 1

Let `(Λ, Σ)` witness `L ≤ K ≤ Λ`, and let `H ≤ K` normalize `Σ`.

- `ΣH` is a subgroup of `Λ`, since `H` normalizes `Σ`.
- **`ΣH ∩ K = LH`.** `⊇`: `L ⊆ Σ`, `H ⊆ H`. `⊆`: if `σh ∈ K` with `σ ∈ Σ`, `h ∈ H ⊆ K`, then `σ ∈ Σ ∩ K = L`.
- **Finiteness.** `H ∩ Σ = H ∩ (K ∩ Σ) = H ∩ L`. So `ΣH/Σ ≅ H/(H ∩ L)`, and `ΣH` is an extension of `Σ` by `H/(H ∩ L)`. If `H ∩ L = 1` it is `Σ ⋊ H`. Both cases are of type `F_m` by (E).
- `Λ` is unchanged. So `(Λ, ΣH)` is an `F_m`-witness for `LH`. ∎

## Step 2. Item 2

- **(i) ⇒ (ii).** `F ≤ N_Λ(Σ)` and `F ∩ Σ = N`. The map `F -> N_Λ(Σ)/Σ` has kernel `F ∩ Σ = N`, so `P` embeds.
- **(ii) ⇒ (i).** Let `P ≤ N_Λ(Σ)/Σ`. Choose `f(a) ∈ N_Λ(Σ)` lifting the image of each generator `a` of `P`. Then `f : F -> N_Λ(Σ)` is a homomorphism with `f^{-1}(Σ) = N`, since `P -> N_Λ(Σ)/Σ` is injective.
  - Put `Λ' = Λ × F` and `Σ' = Σ × F`, of type `F_m` by (P), and embed `F` by `w -> (f(w), w)`.
  - `(f(w), w) ∈ Σ'` iff `w ∈ N`.
  - `(f(w), w)` normalizes `Σ × F`, because `f(w)` normalizes `Σ`.
- **The class.** `Σ = 1` gives type `F_m` groups. For `M ⊴ Γ` take `Σ = M`, `N_Γ(M) = Γ`. Finite `P = F/N` is `F/N` with `F`, `N` free of finite rank. Subgroups: restrict the embedding. Products: `N_{Λ_1 × Λ_2}(Σ_1 × Σ_2) = N(Σ_1) × N(Σ_2)`, with (P). ∎

## Step 3. Item 3

- **(d) ⇒ (d2).** `U = F(B)/<<R>>` with `R` finite, so `J_{N_U} = <<R>> × 1 · ΔF(B) = <R × 1, ΔF(B)>` is finitely generated (Step 2 of the normal-closure proof).
- **(d2) ⇒ (d1).** Let `N ⊴ F(A)` be r.e. and `h : F(A) -> F(B)` with `h^{-1}(N_U) = N` (item 3 of the cited claim). Then `(h × h)^{-1}(J_{N_U}) = {(u, v) : h(u v^{-1}) ∈ N_U} = J_N`. Preimages along `F(A)^2 -> F(B)^2` preserve `F_m`-benignness.
- **(d1) ⇒ (d).** Let `S ≤ F × F` be finitely generated. By Goursat (Step 4 of the normal-closure proof), `S = {(u, v) ∈ P_1 × P_2 : v ∈ λ(u) L}` with `P_i` free of finite rank, `L ⊴ P_2` r.e. and `λ : P_1 -> P_2` a homomorphism.
  - `v ∈ λ(u)L` iff `v^{-1}λ(u) ∈ L` iff `λ(u) v^{-1} ∈ L`, by normality of `L` in `P_2`.
  - So `S = (λ × id)^{-1}(J_L)` with `J_L ≤ P_2 × P_2`, which is benign by (d1).
  - So `S` is benign in `P_1 × P_2`, hence in `F × F` by injective images. ∎

## Step 4. Item 4

- Let `(Λ, Σ)` be an `F`-normalized witness for `N ⊴ F`. Then `(F × Λ, 1 × Σ)` witnesses `1 × N ≤ F × F`.
- `H = ΔF` is free of finite rank, normalizes `1 × Σ` since `(u, u)(1, σ)(u, u)^{-1} = (1, uσu^{-1})`, and `ΔF ∩ (1 × N) = 1`.
- By item 1, `(1 × N)ΔF = J_N` (read with coordinates swapped: `(n u, u)` and `(u, n u)` describe the same fibre product since `N` is normal) is `F_m`-benign.
- If `U` is `F_m`-Weyl, so is every finitely generated recursively presented `G = F(A)/N` (it embeds in `U`, and the class is closed under subgroups). By item 2 each such `N` has a normalized witness, so (d1) holds, hence (d) by item 3, hence the root by item 2 of the normal-closure claim. ∎

## Step 5. Item 5

Let `A ≤ F = F(X)` be r.e., and let `D = F *_A F̄`, presented on `X ⊔ X̄` with relators `w w̄^{-1}`, `w ∈ A`. It is finitely generated and recursively presented. Let `N_D` be its relation subgroup in `F_D = F(X ⊔ X̄)`.

- `φ : F -> F_D × F_D`, `w -> (w, w̄)`, is a homomorphism.
- `φ(w) ∈ J_{N_D}` iff `w w̄^{-1} ∈ N_D` iff the two images of `w` in `D` coincide iff `w ∈ A`. The last step is the normal form theorem for amalgams: the two factors meet exactly in `A`.
- By (d) and item 3, `J_{N_D}` is `F_m`-benign. By preimages, so is `A = φ^{-1}(J_{N_D})`. ∎

## Step 6. The Boone witness is not normalized

If `B` normalized `Σ` in `G'_M`, then `B` would normalize `Σ ∩ B = T_M`.
But `x^{-1} t(a, b) x = t(a + 1, b)`, and `t(s) ∈ T_M` iff `s ∈ Hal` (the
halting subgroup is free on the `t(s)`, `s ∈ Hal`, and the `t(s)` form part of a
free basis of the free group `<t(s) : s ∈ N^2>`). So `x` normalizes `T_M` only
if `Hal` is invariant under `(a, b) -> (a + 1, b)`, which fails for every
machine with some `(a, b) ∈ Hal`, `(a + 1, b) ∉ Hal`, for example every
machine with finite nonempty halting set. So the base-case witness is not of
the kind item 1 needs. ∎
