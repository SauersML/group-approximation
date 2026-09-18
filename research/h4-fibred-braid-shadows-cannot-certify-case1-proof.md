---
rg: 2
id: h4-fibred-braid-shadows-cannot-certify-case1-proof
kind: route
title: Fibred braid shadows send Case 1 hexagons to pure braid hexagons, which always have centres by the Z/2 separation lemma
target: h4-fibred-braid-shadows-cannot-certify-case1-counterexamples
requires:
  - braid-pure-single-edge-hexagons-always-have-a-centre
  - h4-a2-fibred-shadows-are-a4-pure-braid-retractions
  - h4-i25-fibred-shadows-are-rigid-cluster-braid-groups
---

Notation is as in the target and in the three required claims.

## 1. The image hexagons are pure

**`A_2` flats.** By `h4-a2-fibred-shadows-are-a4-pure-braid-retractions` (C):
- `ρ_V : P ↠ P_5` induces a type-preserving simplicial map of single-edge layers into the `A_4` layer for
  `X' = {σ_1,σ_2,σ_3}`, `Y' = {σ_2,σ_3,σ_4}`;
- the vertices are the arcs from puncture 5 to `∂_0` and the arcs from puncture 1 to `∂_1`, and adjacency is
  disjointness.

A Case 1 hexagon `H` has vertices `gA_X`, `gA_Y` with `g ∈ P`. Its image vertices are `ρ_V(g)x_0` and
`ρ_V(g)y_0` with `ρ_V(g) ∈ P_5`. So every image `y`-vertex has leg set `{1}`.

**`I_2(5)` flats.** By `h4-i25-fibred-shadows-are-rigid-cluster-braid-groups` (3)–(4):
- `ρ_V(P) = G_V ⊂ P_7`;
- the map is type-preserving and simplicial into the `A_6` layer for `X'' = {σ_1..σ_5}`,
  `Y'' = {σ_4,σ_5,σ_6}`.

In the arc model of `h4-i25-shadow-centre-forms-hold-only-up-to-rotation-proof` §1, the image vertices are:
- arcs `ρ_V(g)ξ_0` from puncture 7 to `e_0`;
- spiders `ρ_V(g)δ_0` with legs from `e_1` to punctures `1, 2, 3`.

These are pure, since `ρ_V(g) ∈ P_7`. This is the model of `braid-pure-single-edge-hexagons-always-have-a-centre`
with `n = 7`, `k = 3`.

Simplicial maps preserve adjacency. So `ρ_V(H)` is a closed walk `x'_1 y'_{12} x'_2 y'_{23} x'_3 y'_{31}` of
consecutive adjacent vertices, with pure letters.

## 2. Part (1): centres exist

Apply part 3 of `braid-pure-single-edge-hexagons-always-have-a-centre` to `ρ_V(H)`. The spiders `y'_{ij}` have the
same leg set: `{1}` for `A_4`, `{1,2,3}` for `A_6`. So there is a spider with those legs that is adjacent to
`x'_1, x'_2, x'_3`.

Degenerate images are covered by the same part:
- if two `x'_i` coincide, the opposite `y'` is a centre;
- the theorem needs only adjacency, not distinctness.

For a family `(ρ_{V_1},…,ρ_{V_r})`, apply this coordinatewise.

## 3. Part (2): the certificate direction

- If `c = gA_Y` is adjacent to `x_1, x_2, x_3` in the `H_4` layer, then `ρ_V(c)` is adjacent to their images.
- So `ρ_V(H)` centreless implies `H` has no `Y`-type centre.
- By §2 the hypothesis never holds.

**Cabling.** w7-042's cabling `ι : P_4 → P_7` preserves adjacency. It maps pure `A_3` hexagons into `𝓗_V`, and
the `A_3` hexagon has a centre by the theorem (`n = 4`, `k = 1`). This is the conditional statement of
`h4-i25-shadow-centre-forms-hold-only-up-to-rotation` (3), now unconditional. But §2 already covers all of `𝓗_V`
directly, cabled or not.

## 4. Part (3): `A_2` flats and lifting to the image layer

- The centre `y` of §2 has leg set `{1}`, so `y = h y_0` for some `h ∈ B_5` with `h(1) = 1`.
- `A_{Y'} = ⟨σ_2,σ_3,σ_4⟩` maps onto `Sym{2,…,5}`. So there is an `a ∈ A_{Y'}` with the same permutation as `h`,
  and then `h a^{-1} ∈ P_5`.
- Hence `y = (h a^{-1}) y_0 ∈ P_5·y_0 = ρ_V(P)·y_0`.

## 5. Part (4): the `I_2(5)` lifting condition

- `G_V = f^{-1}⟨Δ²_C⟩`, where `f : P_7 → P_C` forgets the strands outside `C`.
- A spider `y` with legs to `1,2,3` is `h y_0` with `h ∈ P_7`, well defined up to `h ↦ ha` with
  `a ∈ A_{Y''} ∩ P_7 = P_{\{4,5,6,7\}}`.
- `f(a)` is a pure braid on the single strand `c+3` of `C ∩ {4,…,7}`, so `f(a) = 1`. Hence `f(h)` depends only on
  `y`.
- So `y ∈ G_V·A_{Y''}` iff `f(h) ∈ ⟨Δ²_C⟩`. This is the forgetful description stated in the target.

Why a proof of Case 1 needs more than a shadow centre:
- `ρ_V` preserves adjacency but need not reflect it. Adjacency of `ρ_V(g)A_{Y''}` to `ρ_V(g_i)A_{X''}` does not
  imply that `gA_Y` meets `g_iA_X` in `P`.
- So a centre in `G_V·A_{Y''}` still has to lift to a vertex that is adjacent in `H_4`, and adjacency there must be checked in `H_4`.
- The tested forms, a hexagon vertex (`y_k`) or a transported twist `D^j A_{Y''}`, are images of layer vertices by
  construction. That is why form (R) is the right target. (R) remains open, and this claim does not prove it.

## 6. What this kills and what it leaves

**Dead.** Every attempt to exhibit a Case 1 counterexample by computing in one or several fibred braid shadows
and finding a centreless image:
- the `A_2` retractions;
- `𝓗_V` for each `I_2(5)` flat;
- cablings into `𝓗_V`;
- products of flats, including `N_V ∩ N_{V'}`.

The step at which each dies is §2: the image hexagon is pure, and pure braid hexagons have centres.

**Left.**
- (L_V)-type lifting certificates in the `I_2(5)` shadows.
- Non-braid (non-fibred) shadows.
- A direct `H_4` argument, such as an `H_4` analogue of the auxiliary arrangements of arXiv:2405.12068 §6.

For a proof, the Z/2 centre construction supplies the candidate centres. What remains is to show that one of them
is a layer image. That is (R).
