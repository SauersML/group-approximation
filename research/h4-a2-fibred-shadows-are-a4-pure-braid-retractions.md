---
rg: 2
id: h4-a2-fibred-shadows-are-a4-pure-braid-retractions
kind: claim
title: Every l_x-fibred shadow of the single-edge H_4 hexagon lives in a pure braid group, and the nine A_2-flat shadows are retractions onto A_4 braid sub-arrangements that see only A_4 single-edge hexagons
distinct_from:
  h4-case1-pure-normal-form-and-fibred-obstruction: that claim builds the fibred 19-wall quotient Q_V and its point-pushing identity; this one computes the monodromy and identifies Q_V's shadow with the retraction onto an A_4 braid arrangement, which kills the A_2 flats as H_4-specific auxiliaries.
---

**Setting.** Notation is as in `h4-case1-pure-normal-form-and-fibred-obstruction`.
- `P` is the pure Artin group of `H_4`, with `X = {s_2,s_3,s_4}`, `Y = {s_1,s_2,s_3}` and `Z = {s_2,s_3}`.
- `F = ker(ρ_X|P_Y)` and `N = ker(ρ_Y|P_X)`.
- `𝒜' = 𝒜_x ∪ 𝒜_y`, and `ℬ` is any sub-arrangement of `𝒜` containing `𝒜'` in which `ℓ_x` is modular. The fibre
  of `M(ℬ) → M(𝒜_x)/ℓ_x` is `ℂ` minus `k` points `p_1(u),…,p_k(u)`.

A single-edge hexagon is a tuple `α_i ∈ F`, `β_i ∈ N` with `α_1α_2α_3 = β_1β_2β_3 = 1` and
`α_1β_1α_2β_2α_3β_3 = 1` in `P`.

**(A) Every fibred shadow is a pure braid shadow.** Write `v = u + t·v_x` with `u ⊥ v_x`. Then
`v ↦ (t, p_1(u), …, p_k(u))` maps `M(ℬ)` into the configuration space `Conf_{k+1}(ℂ)`.
- The map is fibre-preserving and is the identity on fibres.
- So `π_1M(ℬ) → P_{k+1}` is injective on the fibre group `F_k`.
- The hexagon word lies in `F_k`. Hence the hexagon identity holds in `π_1M(ℬ)` iff it holds in
  `P_{k+1} = F_k ⋊ P_k`.
- There the image of `F` is the free factor `⟨A_{i,k+1} : p_i ∈ 𝒜_y∖𝒜_z⟩`. The image of `N` moves only the
  points of `ℬ∖𝒜'` and fixes the `𝒜_y` points.

**(B) The nine `A_2` flats give `A_4`.** Let `V` be one of the 9 `A_2` flats of
`h4-case1-pure-normal-form-and-fibred-obstruction` (C), and `ℬ_V` its 19-wall augmentation.
- The 4 fibre normals are linearly independent. So `(t, p_1, …, p_4)` modulo the diagonal is a linear
  coordinate system on `ℂ^4`.
- In these coordinates the 10 walls `𝒞_V := {4 fibre walls} ∪ {6 collision walls}` are exactly `{q_a = q_b}`:
  the `A_4` braid arrangement. The collision walls are the 3 walls of `𝒜_z` and 3 walls of `𝒜_x∖𝒜_z`.
- `𝒞_V` is not closed under its reflections, so it is not an `A_4` root subsystem. Its trace on `𝒜_x` has the
  combinatorics of `A_3`, which is not a reflection subgroup of `H_3`.
- In the fundamental chamber the real order is `p_4 < p_1 < p_2 < p_3 < t`. Number the strands `1,…,5` in this
  order.

The shadow `P → Q_V → P_5` is the retraction `ρ_V : P ↠ π_1M(𝒞_V) = P_5` induced by `M(𝒜) ⊂ M(𝒞_V)`. The
braid monodromy `μ : P_X → P_4` of `Q_V` on the 15 walls of `𝒜_x` is as follows:
- the 9 walls outside `𝒞_V` go to `1`;
- the 6 walls of `𝒞_V ∩ 𝒜_x` go to the meridians `A_{ij}`, `1 ≤ i < j ≤ 4`, up to conjugacy;
- `ρ_V|P_Y` is an isomorphism onto the parabolic `P_{2345}`, and `ρ_V|P_X : P_X ↠ P_{1234}` is onto;
- hence `ρ_V(F) = F' := ⟨A_{25},A_{35},A_{45}⟩`, isomorphically, and `ρ_V(N) = N' := ⟨A_{12},A_{13},A_{14}⟩`,
  the whole point-pushing group of strand 1.

Every one of the 12 walls of `𝒜_x∖𝒜_z` is a `p_4`-collision wall for some `V`. So the nine shadows jointly see
every meridian of `N`.

**(C) Consequence: the `A_2` shadows are `A_4` in disguise.** Put `X' = {σ_1,σ_2,σ_3}` and
`Y' = {σ_2,σ_3,σ_4}` in `B_5`.
- `ρ_V` induces a type-preserving simplicial map from the single-edge layer `{gA_X, gA_Y : g ∈ P}` of the `H_4`
  Deligne complex to the single-edge layer of the `A_4` Deligne complex for `(X',Y')`.
- A tuple satisfies the `Q_V` identity iff `(ρ_Vα_i, ρ_Vβ_i)` is an `A_4` single-edge hexagon. By surjectivity,
  every `A_4` single-edge hexagon arises this way.
- Use the arc model of `B_5 = Mod(D_5,∂)`, and take `g, h ∈ P_5`.
  - The vertices `gA_{X'}` are the arcs from puncture 5 to a boundary point `∂_0`.
  - The vertices `hA_{Y'}` are the arcs from puncture 1 to a second boundary point `∂_1`.
  - Two vertices are adjacent iff their arcs are disjoint.
- So a shadow hexagon is three arcs from puncture 5 to `∂_0` and three arcs from puncture 1 to `∂_1`. The six
  arcs alternate around the hexagon, and each arc is disjoint from its two neighbours.

So anything the hexagon relation implies inside one `Q_V` is a property of `A_4` single-edge hexagons, and
cannot use the label 5. The `A_2` augmentations are therefore not `H_4` analogues of Huang's auxiliary
arrangement I, which lane w5-042 matched in `H_3` with a fibred `I_2(5)` augmentation. The same holds for
`H_3`: its two `A_2` augmentations (8 walls) are `A_3` braid retractions (`arrangement.py`, function `h3`).

Among single-flat fibred augmentations, the only ones left are the three fibred `I_2(5)` flats (21 walls). For
them:
- the collision walls are 10 planes of `𝒜_x` with `χ(t) = (t−1)(t−4)(t−5)`, a supersolvable arrangement with a
  modular line of 5 planes;
- `𝒞'_V` (16 walls) is fibre-type with exponents `(1,4,5,6)`;
- by (A) the shadow lies in `P_7`, through a linear section of the `A_6` braid arrangement that is not the
  whole of it.

Proof: `h4-a2-fibred-shadows-are-a4-pure-braid-retractions-proof`. Computations:
`experiments/h4-case1-braid-monodromy-2026-09-17/` (`arrangement.py`, `i25probe.py` and logs). Lane w6-042,
2026-09-18, unreviewed.
