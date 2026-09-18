---
rg: 2
id: h4-fibred-braid-shadows-cannot-certify-case1-counterexamples
kind: claim
title: No fibred braid shadow (A_2 or I_2(5) flat, or a product of them) can certify a centreless single-edge H_4 hexagon by showing its image centreless, since every image hexagon has a centre; what is left of Case 1 is a lifting problem
distinct_from:
  h4-i25-shadow-centre-forms-hold-only-up-to-rotation: that shows the base-edge centre forms fail but hold up to rotation on tested tuples, and kills the cabling route conditionally; this proves that image hexagons always have centres, unconditionally and for every fibred braid shadow.
  h4-case1-pure-normal-form-and-fibred-obstruction: that obstructs sub-arrangements of A_x ∪ A_y; this obstructs the fibred augmentations that replaced them, as certificates of centrelessness.
---

**Setting.**
- A *Case 1* (single-edge) hexagon of `h4-deligne-complex-bottom-triples-have-upper-bounds` is a 6-cycle
  `x_1 y_{12} x_2 y_{23} x_3 y_{31}` in the layer `{gA_X, gA_Y : g ∈ P}`. Here `P` is the pure `H_4` Artin
  group, `X = {s_2,s_3,s_4}` and `Y = {s_1,s_2,s_3}`.
- A *fibred braid shadow* is one of the maps `ρ_V` of:
  - `h4-a2-fibred-shadows-are-a4-pure-braid-retractions`: `ρ_V : P ↠ P_5`, into the `A_4` layer for
    `(X',Y')`;
  - `h4-i25-fibred-shadows-are-rigid-cluster-braid-groups`: `ρ_V : P ↠ G_V ⊂ P_7`, into the `A_6` layer for
    `(X'',Y'')`.
- Each induces a type-preserving simplicial map of layers `gA_X ↦ ρ_V(g)A_{X'}`, `gA_Y ↦ ρ_V(g)A_{Y'}`. So it
  sends Case 1 hexagons to single-edge braid hexagons whose letters are pure.

**Claim.**
1. **(Images always have centres.)** For every fibred braid shadow `ρ_V` and every Case 1 hexagon `H`, the image
   `ρ_V(H)` has a centre in the braid layer. The centre is a spider of type `Y'` or `Y''` adjacent to all three
   image `x`-vertices, and its legs run to the standard punctures (`{1}` or `{1,2,3}`).

   The same holds for any finite family of shadows at once, `(ρ_{V_1}, …, ρ_{V_r})`, for example two `I_2(5)` flats
   `N_V ∩ N_{V'}`. Each coordinate image has centres.
2. **(So no image-centrelessness certificate exists.)**
   - If `H` has a centre `c = gA_Y`, then `ρ_V(c)` is a centre of `ρ_V(H)`.
   - Hence "`ρ_V(H)` has no centre" would certify that `H` has no `Y`-type centre.
   - By (1) this certificate is never available: not for cabled hexagons, not for any hexagon in the class `𝓗_V`,
     and not for multi-flat products.
   - In particular, w7-042's cabling route (`ι : P_4 → P_7`), which was dead there conditionally on the `A_3` pair
     lemma, is dead **unconditionally**.
3. **(For the `A_2` flats, even the finer certificate is dead.)**
   - `ρ_V : P ↠ P_5` is onto. Every spider `h y_0` with `h(1) = 1` lies in `P_5·A_{Y'}`, because `A_{Y'}` realises
     every permutation of `{2,…,5}`.
   - So some image centre lies in the image layer `ρ_V(P)A_{Y'}`. No `A_2` shadow can witness even "no image
     centre lifts to the layer".
4. **(What is left of Case 1.)** A shadow certificate for a counterexample must use the *lifting* failure. Only one
   form survives, in the `I_2(5)` shadows:
   - **(L_V)** no centre of `ρ_V(H)` lies in `G_V·A_{Y''}`.
   - In the arc model, (L_V) says the following. The centres are the spiders with legs to `1,2,3` inside the
     `d_1`-region `Ω(x_1 ∪ x_2 ∪ x_3)`. Forget all punctures outside the cluster `C = {1,2,3,c+3}`. Then no such
     spider becomes `Δ_C^{2j}y_0` for any `j`. (`f(P_{4567}) = 1` on `C`, so this condition is independent of the
     coset representative.)
   - A proof of Case 1 must instead show that a centre of `H` itself exists. For a shadow proof that means a
     centre in `G_V·A_{Y''}` that moreover lifts to an `H_4`-adjacent vertex, since `ρ_V` preserves adjacency but
     need not reflect it. That
     is the rotation-invariant form (R) of `h4-i25-shadow-centre-forms-hold-only-up-to-rotation`. On every tested
     tuple (R) is realised by a hexagon vertex or a transported twist, and both lie in `G_V·A_{Y''}`.

**Why it holds.**
- Image hexagons are pure single-edge braid hexagons.
- `braid-pure-single-edge-hexagons-always-have-a-centre` (the `Z/2` separation lemma) gives every such hexagon a
  centre: a spider with legs to the common leg set, inside the `d_1`-region of the three `x`-arcs.

The full argument is in `h4-fibred-braid-shadows-cannot-certify-case1-proof`.

**Status.** Established, modulo the cited shadow identifications. Those are unreviewed lane results; see the route.
