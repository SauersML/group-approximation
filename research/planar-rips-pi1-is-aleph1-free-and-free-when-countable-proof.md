---
rg: 2
id: planar-rips-pi1-is-aleph1-free-and-free-when-countable-proof
kind: route
title: "Proof: stable images of finite stages are free factors of each other by the planar free-factor lemma, and countable subgroups lie in chain unions of them"
target: planar-rips-pi1-is-aleph1-free-and-free-when-countable
requires:
  - planar-rips-projection-is-a-pi1-isomorphism
  - planar-polyhedron-inclusions-have-free-factor-pi1-images
artifacts:
  - research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md
---

Write `R(Y) = R_r(Y)` in the chosen convention. Fix `x_0 ∈ X` and put
`G = π_1(R(X), x_0)`. Let `𝓕` be the directed set of finite `F ⊆ X` with
`x_0 ∈ F`. Write `π(F) = π_1(R(F), x_0)`.

## Step 0: colimit and shadows

- **Colimit.** `R(F)` is a full subcomplex of `R(F′)` for `F ⊆ F′`. Loops and
  homotopies have compact image, so they lie in finite subcomplexes, and hence
  in some `R(F)`. Therefore `G = colim_{F ∈ 𝓕} π(F)`, a directed colimit: an
  element of `π(F)` is trivial in `G` if and only if it is trivial in some
  `π(F′)` with `F′ ⊇ F`.
- **Shadows.** Let `p_F : |R(F)| → R^2` be the affine extension of `F ⊆ R^2`,
  and let `K_F` be the component of the shadow `p_F(|R(F)|)` containing `x_0`.
  - `K_F` is a compact connected planar polyhedron.
  - By `planar-rips-projection-is-a-pi1-isomorphism` (finite sets, either
    convention), `p_F` induces an isomorphism `π(F) ≅ π_1(K_F, x_0)`. In
    particular `π(F)` is free of finite rank.
- **Naturality.** For `F ⊆ F′`, `p_{F′}` restricts to `p_F` on `R(F)`, so
  `K_F ⊆ K_{F′}`. The map `π(F) → π(F′)` corresponds to the map induced by the
  inclusion `K_F ⊆ K_{F′}`.
- **Consequence (A).** By `planar-polyhedron-inclusions-have-free-factor-pi1-images`,
  for all `F ⊆ F′` in `𝓕` the image
  `I(F, F′) = im(π(F) → π(F′))` is a free factor of `π(F′)`.

## Step 1: stable images

This step repeats the artifact
`research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md` §6.

- **Ranks do not increase.** Fix `F`. For `F ⊆ F′ ⊆ F″`, the group
  `I(F, F″)` is the image of `I(F, F′)`. All these are finitely generated free
  groups, and abelianizing shows that the rank does not increase.
- **Stable stage.** Choose `F* ⊇ F` of minimal rank `ρ_F`. For `F′ ⊇ F*`, the
  surjection `I(F, F*) → I(F, F′)` is between free groups of rank `ρ_F`, so it
  is an isomorphism because free groups of finite rank are Hopfian.
- **Consequence (B).** By the colimit description, `I(F, F*) → G` is
  injective. Let `J_F` be its image, which is the image of `π(F)` in `G`. Then
  for every `F′ ⊇ F*` the map `I(F, F′) → J_F` is an isomorphism, because it is
  the composite of the inverse of `I(F, F*) ≅ I(F, F′)` with
  `I(F, F*) ≅ J_F`.
- **Directed union.** `J_F ⊆ J_E` for `F ⊆ E`, and `G = ⋃_{F ∈ 𝓕} J_F` is a
  directed union.

## Step 2: free factors inside subgroups

**Fact (Kurosh).** Suppose `A` is a free factor of a group `B` and
`A ≤ C ≤ B`. Then `A` is a free factor of `C`.

*Proof.*

1. Write `B = A * A′` and let `T` be the Bass–Serre tree of this splitting. It
   has trivial edge stabilisers, and vertex stabilisers are the conjugates of
   `A` and `A′`.
2. Let `v` be the vertex with stabiliser `A`. Then `C_v = C ∩ A = A`.
3. `C` acts on `T` with trivial edge stabilisers. Choose a lift of a maximal
   tree of `C∖T` that contains `v`; a lift may be started at any vertex.
4. The structure theorem gives
   `C = (∗_{u} C_u) * F(Y)`, where `u` runs over the vertices of the lifted
   tree and `F(Y)` is free. The factor `C_v = A` is one of the `C_u`. ∎

**Lemma (C).** For `F ⊆ E` in `𝓕`, `J_F` is a free factor of `J_E`.

*Proof.*

1. Choose `H ∈ 𝓕` with `H ⊇ F* ∪ E*`. Then `H ⊇ E ⊇ F`.
2. In `π(H)` we have `I(F, H) ≤ I(E, H) ≤ π(H)`.
3. By (A), `I(F, H)` is a free factor of `π(H)`. By the Kurosh fact it is a
   free factor of `I(E, H)`.
4. Since `H ⊇ E*`, (B) says `I(E, H) → J_E` is an isomorphism. It carries
   `I(F, H)` onto the image of `π(F)` in `G`, which is `J_F`. ∎

## Step 3: countable subgroups

- **Exhausting chain.** Let `C ≤ G` be countable, `C = {g_1, g_2, …}`. By the
  directed union in Step 1, choose `E_1 ⊆ E_2 ⊆ ⋯` in `𝓕` with
  `g_1, …, g_n ∈ J_{E_n}`. Then `C ≤ U = ⋃_n J_{E_n}`.
- **A basis of `U`.**
  - By Lemma (C), `J_{E_{n+1}} = J_{E_n} * V_n`. Here `V_n` is free as a
    subgroup of a free group, and the `J_{E_n}` are free of finite rank by
    Step 1.
  - Let `B_1` be a basis of `J_{E_1}`. Let `B_{n+1}` be `B_n` together with a
    basis of `V_n`. Then `B_n` is a basis of `J_{E_n}` for every `n`.
  - The union `B = ⋃ B_n` generates `U`. A nontrivial reduced word in `B` uses
    finitely many letters, so it lies in some `B_n` and is nontrivial in
    `J_{E_n}`.
  - So `B` is a basis and `U` is free.
- **Conclusion.** `C ≤ U` is free by Nielsen–Schreier. This proves part 1.
- **Part 2.** If `G` is countable, take `C = G`. If `X` is countable, then `𝓕`
  is countable and each `π(F)` is finitely generated, so `G` is countable.
- **Other base points.** A base point in `|R(X)|` that is not a vertex is
  joined by a path to a vertex, which lies in `X`. ∎

## Remarks

- The argument never needs `J_F` to be a free factor of `G`. It uses only
  pairwise free-factor relations between stable images, and that is exactly
  why it stops at countable subgroups (see the Attempts of the target claim).
- The abelianized statement is consistent with
  `planar-rips-complexes-have-free-first-homology`. For countable `X`,
  `H_1(R(X))` is the abelianization of a free group, hence free abelian; that
  claim covers every `X` by a different route.
