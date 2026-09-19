---
rg: 2
id: bader-shalom-hosting-factors-are-totally-disconnected-proof
kind: route
title: "Proof: a factor with nontrivial identity component is almost connected by just-non-compactness and receives the injective projection of S, which Gleason-Yamabe plus Malcev forbid; in the totally disconnected case, intersecting the lattice with a compact-open-times-factor subgroup gives the lattice data"
target: bader-shalom-hosting-factors-are-totally-disconnected
requires:
  - bader-shalom-normal-subgroup-theorem
  - almost-connected-groups-omit-fg-infinite-simple-groups
  - gleason-yamabe-and-van-dantzig-structure-theorems
  - fg-infinite-simple-groups-are-minimally-almost-periodic
---

Notation is as in the target. `G = G_1 × G_2`. By NST item 2 of
`bader-shalom-normal-subgroup-theorem`, `p_1` and `p_2` are injective on `Γ`.

## Item 1

- `G_i^0` is a closed normal subgroup of `G_i`. It is closed because components
  are closed, and normal because conjugations are homeomorphisms fixing `1`.
- Suppose `G_i^0 ≠ 1`. Then `G_i/G_i^0` is a proper Hausdorff quotient of
  `G_i`, so it is compact by just-non-compactness. Hence `G_i` is almost
  connected.
- By `almost-connected-groups-omit-fg-infinite-simple-groups`, item 2,
  the homomorphism `p_i|_S : S → G_i` is trivial. But it is injective and
  `S ≠ 1`, a contradiction.
- So `G_i^0 = 1`. By homogeneity every component of `G_i` is a point, so `G_i`
  is totally disconnected.

## Item 2

Item 1 makes `G_1` totally disconnected. So a compact open subgroup `U_1` exists
by `gleason-yamabe-and-van-dantzig-structure-theorems`, item 3. Put
`O = U_1 × G_2`, an open subgroup of `G`, and `Λ = Γ ∩ O`.

**(a1) `Λ` is cocompact in `O`.**
- `O` acts on `Γ\G` on the right. Each orbit `Γ\ΓgO` is open, being the image
  of the open set `ΓgO` under the open quotient map.
- The orbits are disjoint and cover the compact space `Γ\G`. So there are
  finitely many, and each is also closed, hence compact.
- The map `Λ\O → Γ\ΓO`, `Λo ↦ Γo`, is well defined, continuous and bijective.
  It is injective because `Γo = Γo'` with `o, o' ∈ O` gives `o'o^{-1} ∈ Γ ∩ O`.
- It is open: for `W ⊆ O` open and left `Λ`-saturated, the image is the image of
  the open set `ΓW ⊆ G`.
- So `Λ\O` is homeomorphic to a compact orbit, and it is compact.

**(a2) `Δ_2 = p_2(Λ)` is discrete.**
- Let `V` be a compact neighbourhood of `1` in `G_2`. Then `U_1 × V` is compact
  and `Γ` is discrete, so `F = Λ ∩ (U_1 × V)` is finite.
- Since `p_1(Λ) ⊆ U_1`, we have `Δ_2 ∩ V = p_2(F)`, which is finite.
- A Hausdorff group whose identity has a neighbourhood meeting a subgroup in a
  finite set sees that subgroup as discrete.

**(a3) `Δ_2` is cocompact.** The map `Λ\O → Δ_2\G_2`, `Λo ↦ Δ_2 p_2(o)`, is well
defined, continuous and onto, because `p_2(O) = G_2`. So `Δ_2\G_2` is compact.

**(a4) `Δ_2` is a lattice.**
- `G` has the lattice `Γ`, so `G` is unimodular. The modular function of a
  product is the product of the modular functions, so `G_2` is unimodular.
- A discrete subgroup of a unimodular group gives an invariant measure on the
  quotient. For `Δ_2\G_2` this measure is finite, because the quotient is
  compact.
- `p_2|_Λ` is injective by NST item 2, so `p_2 : Λ → Δ_2` is an isomorphism.
  This proves (a).

**(b)** `p_1(Λ) ⊆ U_1` and `p_1|_Λ` is injective. So `p_1 ∘ (p_2|_Λ)^{-1}` embeds
`Δ_2` in the compact group `U_1`.

**(c) Commensuration.**
- `p_2(Γ)` is dense by hypothesis.
- For `γ ∈ Γ`, the subgroup `V_γ = U_1 ∩ p_1(γ) U_1 p_1(γ)^{-1}` is open in the
  compact group `U_1`, so it has finite index there.
- `Λ ∩ γΛγ^{-1} = Γ ∩ (V_γ × G_2)` is the stabilizer in `Λ` of the point `V_γ`
  of the finite `U_1`-set `U_1/V_γ`, acting through `p_1`. So it has finite index
  in `Λ`.
- Applied to `γ^{-1}`, it also has finite index in `γΛγ^{-1}`. Applying the
  injective `p_2` gives the commensuration of `Δ_2` by `p_2(Γ)`.

**(c) Index.**
- `γΛ = γ'Λ` iff `p_1(γ^{-1}γ') ∈ U_1`. So `[Γ : Λ]` is the size of the orbit
  `p_1(Γ)U_1` in `G_1/U_1`.
- Each coset `gU_1` is open and `p_1(Γ)` is dense, so the orbit is all of
  `G_1/U_1`.
- That set is infinite: finitely many cosets of the compact `U_1` would make
  `G_1` compact.
- So `[p_2(Γ) : Δ_2] = [Γ : Λ] = ∞`, using the injectivity of `p_2`.

The exchanged statement has the same proof, using item 1 for `G_2`.

## Item 3

Take `i = 1`; the case `i = 2` is symmetric. Put `S_1 = S ∩ (U_1 × G_2)`.

**Embeds in a compact group.** `p_1(S_1) ⊆ U_1` and `p_1` is injective, so `S_1`
is isomorphic to a subgroup of `U_1`.

**Commensurated.** For `s ∈ S`, the argument of (c) with `γ = s` shows that
`S_1 ∩ sS_1s^{-1} = S ∩ (V_s × G_2)` has finite index in both `S_1` and
`sS_1s^{-1}`.

**Infinite index.**
- If `[S : S_1] < ∞`, the normal core of `S_1` in `S` is a normal subgroup of
  finite index. It is nontrivial because `S` is infinite, so it equals `S`.
- Then `S ⊆ S_1`, and `p_1|_S` is an injective homomorphism into the compact
  group `U_1`. It is nontrivial, which contradicts
  `fg-infinite-simple-groups-are-minimally-almost-periodic`.

**Dichotomy.**
- If `p_1(S)` is discrete, it is closed, so `p_1(S) ∩ U_1` is finite. By
  injectivity `S_1` is finite.
- Conversely, if `S_1` is finite, then `F = p_1(S) ∩ U_1` is finite. So
  `U_1 \ (F \ {1})` is a neighbourhood of `1` meeting `p_1(S)` only in `1`, and
  `p_1(S)` is discrete.

This proves the dichotomy (D)/(N).

## Item 4

Suppose `Γ` is a Bader–Shalom lattice in `G_1 × G_2` containing a finitely
generated infinite simple `S`.
- Item 1 makes both factors totally disconnected.
- Item 2 and its exchanged form then give each factor a cocompact lattice that
  embeds in a compact group.

The contrapositive is item 4. ∎

**Trust surface.**
- The imports are:
  - NST item 2, as cited in the graph;
  - van Dantzig and Gleason–Yamabe, verbatim through Tao's notes;
  - minimal almost periodicity, established.
- Point-set facts used without citation:
  - components are closed;
  - quotient maps by closed subgroups are open;
  - discrete subgroups are closed;
  - unimodularity is inherited by the factors of a product that has a lattice;
  - discrete subgroups of unimodular groups give invariant quotient measures.
