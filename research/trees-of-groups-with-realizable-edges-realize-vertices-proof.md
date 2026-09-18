---
rg: 2
id: trees-of-groups-with-realizable-edges-realize-vertices-proof
kind: route
title: Nest witnesses by the swap lemma for transitivity, glue two witnesses along a common edge subcomplex for amalgams, and build trees by transfinite leaf-attachment with directed unions at limits
target: trees-of-groups-with-realizable-edges-realize-vertices
requires:
  - relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two
  - continuous-free-chain-unions-have-gd-two
  - relative-eg-pair-base-meets-its-conjugates-in-free-groups
  - relative-countable-eg-gives-eg-for-aleph-one-groups
---

We use from `relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two-proof`: the swap lemma (a) ⇒ (b) and the facts (F5) (Whitehead gluing) and (F6) (directed unions of aspherical subcomplexes are aspherical with `π_1` the colimit). None of these uses countability. Base points and based attaching maps are chosen throughout so that the `π_1` identifications are compatible.

## (T1) Transitivity

Let `K_A ⊆ X_B` witness `RP(A,B)`. `X_B` is a 2-dimensional `K(B,1)`, so by `RP(B,C)` and the swap lemma there is a 2-dimensional `K(C,1)` `X_C ⊇ X_B` inducing `B ≤ C`. Then `K_A ⊆ X_C` is an aspherical subcomplex, and `K_A ↪ X_C` induces the composite `A ≤ B ≤ C`. ∎

## (D) Descent

Let `K ⊆ X'` witness `RP(H,G')` and let `q: X̂ → X'` be the covering corresponding to `G ≤ G'`. `X̂` is a 2-dimensional `K(G,1)`. By (F3) of the engine proof, the component `K̂` of `q^{-1}(K)` through the base lift is a subcomplex with `π_1 K̂ = H ∩ G = H`, mapping injectively onto `H ≤ G`. `K̂ → K` is the covering for `H ∩ G = H`, i.e. an isomorphism, so `K̂` is aspherical. ∎

- *Overgroup form.* `⇒` is trivial with `G' = G`.
- *Amalgams.* `RP(H,G) ⇒ RP(H,Γ_κ)`: by (b) ⇒ (d) of the engine, the glued complex `Z_κ` contains `K`. `RP(H,Γ_κ) ⇒ RP(H,G)` is (D) with `G = G_0 ≤ Γ_κ`. ∎

## (T2) Amalgams

Let `K_C ⊆ X_A` witness `RP(C,A)`. By `RP(C,B)` and the swap lemma applied to the base `K_C`, there is a 2-dimensional `K(B,1)` `X_B ⊇ K_C` inducing `C ≤ B`. Set `Z = X_A ∪_{K_C} X_B`.

- `Z` is a 2-dimensional CW complex with `X_A ∩ X_B = K_C`.
- `K_C`, `X_A`, `X_B` are connected and aspherical and `C` injects into `A` and `B`, so by (F5) `Z` is aspherical with `π_1 Z = A *_C B`.
- `X_A ⊆ Z` and `X_B ⊆ Z` are aspherical subcomplexes inducing the canonical inclusions (normal form theorem). ∎

## (R) Trees

Well-order the vertices as `(v_α)_{α<μ}` so that each `T_α = {v_β : β < α}` (for `α ≥ 1`) spans a subtree. This is possible for a connected graph by transfinite recursion: at stage `α`, pick a vertex adjacent to `T_α` if `T_α` is not everything. Since `𝒯` is a tree, each `v_α` with `α ≥ 1` is adjacent to exactly one vertex of `T_α`, through one edge `e_α`. Put `T_{α+1} = T_α ∪ {v_α}`, `T_λ = ⋃_{α<λ} T_α` for limits, and `G_α = π_1(𝒯|T_α)`. Standard Bass–Serre facts: `G_{α+1} = G_α *_{C_{e_α}} G_{v_α}`, and `G_λ = ⋃_{α<λ} G_α` is the directed union.

We prove by induction on `α ≥ 1`:

**P(α):** `RP(G_u, G_α)` for every `u ∈ T_α`.

- **`α = 1`.** `G_1 = G_{v_0}`; `RP(B,B)` holds for any `B` with a 2-dimensional `K(B,1)`, and `G_{v_0}` has one because some edge hypothesis `RP(C_e, G_{v_0})` provides it (if `𝒯` is a single vertex, (R) needs `gd G_v ≤ 2`, which we add as a hypothesis in that degenerate case).
- **Successor.** Let `v = v_α`, `e = e_α`, `u` the neighbour in `T_α`, `C = C_e`.
  - By P(α), `RP(G_u, G_α)`; with `RP(C, G_u)`, (T1) gives `RP(C, G_α)`.
  - With `RP(C, G_v)`, (T2) gives `RP(G_α, G_{α+1})` and `RP(G_v, G_{α+1})`.
  - For old `u' ∈ T_α`, (T1) with P(α) gives `RP(G_{u'}, G_{α+1})`. So P(α+1).
  - Record: `RP(G_α, G_{α+1})` holds for every `α` with P(α). (∗)
- **Limit `λ`.** Fix `u ∈ T_λ`, say `u ∈ T_{α_0}` with `α_0` a successor. Build 2-dimensional complexes `Z_α`, `α_0 ≤ α ≤ λ`, each a `K(G_α,1)`, with `Z_β ⊆ Z_α` inducing `G_β ≤ G_α`:
  - `Z_{α_0}` is a witness for P(α_0) at `u`, i.e. it contains an aspherical subcomplex `K_u` carrying `G_u`.
  - Successor: by (∗) (P(α) holds for `α < λ` by induction), `RP(G_α,G_{α+1})`; the swap lemma with base `Z_α` gives `Z_{α+1} ⊇ Z_α`.
  - Limit `μ ≤ λ`: `Z_μ = ⋃_{α<μ} Z_α`, which by (F6) is a 2-dimensional `K(G_μ,1)`.
  Then `K_u ⊆ Z_λ` witnesses `RP(G_u, G_λ)`, so P(λ).

Since `T_μ` is the whole tree, P(μ) is (R). ∎

## (R') Free loop edges

Let `T` be the maximal tree and `G_T = π_1(𝒢|T)`. Then `π_1 𝒢` is the fundamental group of the graph of groups with the single vertex `G_T` and one loop for each edge outside `T`, with the same free edge groups. By (R), `RP(G_v, G_T)`, so `G_T` has a 2-dimensional `K(G_T,1)`. Lemma 2 of `continuous-free-chain-unions-have-gd-two-proof` (vertex `v_0` carrying `G_T`, free edge groups, no other vertices) gives `RP(G_T, π_1 𝒢)` for any chosen base complex. (T1) gives `RP(G_v, π_1 𝒢)`. ∎

## (M3) Peripheral 3-manifold pairs

- **`∂M ≠ F` ⇒ RP.** Let `∂' = ∂M ∖ F ≠ ∅`. A handle decomposition of `M` relative to `F` (built on a collar `F × I`) can be taken without 3-handles: turned upside down it is a decomposition relative to `∂'` whose 0-handles cancel against 1-handles because `M` is connected and `∂' ≠ ∅`. Collapsing each handle to its core and the collar to `F` gives a 2-dimensional CW complex `X = F ∪ e^1 ∪ e^2 ≃ M` containing `F` as a subcomplex, with `F ↪ X` inducing `H ≤ G`. `X` is aspherical since `M` is, and `F` is aspherical (genus `≥ 1`) and incompressible. So `RP(H,G)`.
- **RP ⇒ admissible.** This is the necessity of the pd hypothesis (`relative-countable-eg-gives-eg-for-aleph-one-groups`, via `C_*(X̃, p^{-1}F)`).
- **Admissible ⇒ `∂M ≠ F`.** If `∂M = F`, then `[F] = ∂[M] = 0` in `H_2(M) = H_2(G)`, while `H_2(H) = H_2(F) ≅ Z` is generated by `[F]`. So `H_2(H) → H_2(G)` is zero, and part (B) of `relative-eg-pair-base-meets-its-conjugates-in-free-groups` shows `pd I_{G/H} ≥ 2`. ∎

## The tower remark

If `RP(G,G')`, then `RP(H,G) ⇒ RP(H,G')` by (T1) and `RP(H,G') ⇒ RP(H,G)` by (D).

## Calibration

- **Free edge groups on a tree.** `RP(C,B)` for free `C` and `gd B ≤ 2` is Lemma 1 of `continuous-free-chain-unions-have-gd-two-proof`, so (R) recovers Lemma 2 there for trees, and (R') recovers it in general.
- **A failing edge must fail.** Take `𝒯` the single edge `Z^2 — Z^2` with `C = Z^2`, `G_u = Z^2`, and `G_w = K` the Klein bottle group containing `C` with index 2. Then `RP(C, G_w)` fails (pd condition), and indeed `π_1 𝒯 = K` and `RP(Z^2, K)` fails. The theorem makes no claim here, as required.
- **Consistency with `relative-eg-pair-base-meets-its-conjugates-in-free-groups`.** In `A *_C B`, for `b ∈ B ∖ C` Bass–Serre theory gives `A ∩ bAb^{-1} = C ∩ bCb^{-1}`, and `RP(C,B)` gives `pd I_{B/C} ≤ 1`, so that intersection is free, as admissibility of `(A, A *_C B)` requires.
