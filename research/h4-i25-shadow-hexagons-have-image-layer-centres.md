---
rg: 2
id: h4-i25-shadow-hexagons-have-image-layer-centres
kind: claim
title: Every I_2(5) shadow hexagon has a centre in the image layer G_V·A_{Y''} (ejection-arc lemma), so the lifting certificate (L_V) never holds and single I_2(5) shadows reduce Case 1 exactly to reflecting adjacency through ker ρ_V
distinct_from:
  h4-fibred-braid-shadows-cannot-certify-case1-counterexamples: that proves image hexagons have some centre (any pure spider in the d_1-region) and leaves (L_V), "no centre lies in G_V·A_{Y''}", as the one surviving I_2(5) certificate; this proves a centre always lies in G_V·A_{Y''}, which kills (L_V).
  braid-pure-single-edge-hexagons-always-have-a-centre: that is the Z/2 Helly lemma for the region R(X); this controls the forgotten cluster class f(h) of the centre, which Helly alone does not see.
---

**Setting.** Notation is as in `h4-i25-fibred-shadows-are-rigid-cluster-braid-groups` and the arc model of
`braid-pure-single-edge-hexagons-always-have-a-centre`, with `n = 7` and `k = 3`.
- `D` is a disc with punctures `1,…,7` and boundary marks `d_0, d_1`.
- `x`-vertices are arcs from puncture 7 to `d_0`, with `ξ_0` the standard one.
- `y`-vertices of type `Y'' = {σ_4,σ_5,σ_6}` are spiders from `d_1` to `1,2,3`, with `δ_0` the standard one.
  Every such spider is `hδ_0` with `h ∈ P_7`, and `h` is unique up to `h ↦ ha` with `a ∈ P_{4567}`.
- `C = {1,2,3,c}` is the rigid cluster, where `c = c+3 ∈ {4,5,6}` is the strand of `p_c`.
  `f : P_7 → P_C` forgets the strands outside `C`, and `D = Δ²_C`.
  `G_V = f^{-1}⟨D⟩ = ρ_V(P)`.
- `f(P_{4567}) = 1`, so `f(h)` depends only on the spider `y = hδ_0`. The *image layer* is
  `G_V·A_{Y''} = {y : f(h) ∈ ⟨D⟩}`.

**Theorem (ejection-arc lemma).** Let `x_1, x_2, x_3` be any arcs from 7 to `d_0`. Suppose that for each pair
`ij` there is a spider `y_{ij} = h_{ij}δ_0` in the image layer, `f(h_{ij}) = D^{m_{ij}}`, that is disjoint from
`x_i` and `x_j`. Then:
1. **(Image-layer centre.)** Some spider `y = hδ_0` with `f(h) ∈ ⟨D⟩` is disjoint from `x_1, x_2, x_3`.
   - If `p_c ∈ R(x_1∪x_2∪x_3)`, then for every `j ∈ ℤ` there is such a centre with `f(h) = D^j`.
   - If `p_c ∉ R(x_1∪x_2∪x_3)`, the centre can be taken with `f(h) = D^m`, where `m` is given in (2).
2. **(Rigidity when `p_c` is ejected.)** Suppose `p_c ∉ R(x_1∪x_2∪x_3)`. Let `O` be the set of pairs with
   `p_c ∉ R(x_i∪x_j)`; it is non-empty by Helly.
   - **(P1)** All `m_{ij}` with `ij ∈ O` are equal. Call the common value `m`.
   - **(P2)** Every centre `y = hδ_0`, image layer or not, has `f(h) ∈ D^m·P_{123}`, where `P_{123} ⊂ P_C` is the
     pure braid group of the cable `{1,2,3}`. In particular:
     - every image-layer centre has `f(h) = D^m`;
     - a twist `D^jδ_0` is a centre only if `j = m`;
     - a hexagon vertex `y_{ij}` is a centre only if `m_{ij} = m`.

**Consequences for Case 1.**
- **(a) (L_V) never holds.** For every `I_2(5)` flat `V` and every Case 1 hexagon `H` of
  `h4-deligne-complex-bottom-triples-have-upper-bounds`, the image `ρ_V(H)` has a centre in `G_V·A_{Y''}`.
  - Apply the theorem with `x_i = ρ_V(p_i)ξ_0` and `y_{ij} = ρ_V(u_{ij})δ_0`, where `u_{ij}A_Y` are the
    `y`-vertices of `H`. These are images of layer vertices, and `ρ_V(u_{ij}) ∈ ρ_V(P) = G_V`.
  - So (L_V), the one certificate left open by `h4-fibred-braid-shadows-cannot-certify-case1-counterexamples`
    (4), is never available.
  - Every single-flat fibred certificate is now dead. This includes the finer lifting certificate, as it
    already was for the `A_2` flats.
- **(b) Group form.** Adjacency of an image-layer spider `hA_{Y''}` (`h ∈ G_V`) to `ρ_V(p_i)A_{X''}` is
  equivalent to `h ∈ ρ_V(p_iP_XP_Y)`, since `G_V ∩ P_{X''}P_{Y''} = G^X_V·P_{4567} = ρ_V(P_XP_Y)`. So (a) says
  `⋂_i ρ_V(p_iP_XP_Y) ≠ ∅`.
  - Case 1 itself is `⋂_i p_iP_XP_Y ≠ ∅` in `P`.
  - So after (a), the single-flat shadow problem is exactly whether `ρ_V` reflects this intersection, i.e. a
    statement about `ker ρ_V`. The lift in part (b) of the brief's (L_V) step is *equivalent* to Case 1 and
    cannot come from a single shadow.
- **(c) What stays live.** The joint image of several flats. For two flats `V, V'`, the image of
  `(ρ_V, ρ_{V'})` is not the product `G_V × G_{V'}`. So the coordinatewise statement of
  `h4-fibred-braid-shadows-cannot-certify-case1-counterexamples` (1) does not produce a *joint* image-layer
  centre. The theorem gives image-layer centres `h_V, h_{V'}` separately. A joint certificate needs a single
  `g ∈ P` with `ρ_V(g) ∈ ⋂ρ_V(p_iP_XP_Y)` and `ρ_{V'}(g) ∈ ⋂ρ_{V'}(p_iP_XP_Y)`.
  - By (P2), when `p_c` is ejected the forgotten class of every such centre is pinned, to `D^m` resp. `D'^{m'}`.
  - That makes the two-flat joint problem a finite compatibility question.
  - It has no braid-group model with two rigid clusters. For every pair of the three flats, `ℓ_x` is not
    modular in `ℬ_V ∪ ℬ_{V'}` (23 walls, 8 fibre points). The extra cluster points of `V` and `V'` collide on 2
    hyperplanes that are not `H_4` walls (`twoflat.py`, `twoflat.log` in the experiment folder).
  - So the joint shadow is the non-fibre-type group `π_1M(ℬ_V ∪ ℬ_{V'})`.

**Why it holds (sketch).**
- Let `Z` be the complement of the `d_1`-region `Ω` of `x_1∪x_2∪x_3`. Its regular neighbourhood `E` is a disc at
  `d_0`, and it contains no puncture of `{1,2,3}` (Helly).
- If `E` misses `p_c`: after forgetting the strands outside `C`, `E` is an unpunctured half-disc. Every spider,
  in particular `D^jδ_0`, can be pushed off it into `Ω`, and then off the forgotten punctures.
- If `E` contains `p_c`: the arc `ε` in `E` from `p_c` to `d_0` is unique in the forgotten disc. It is also the
  ejection arc of each pair in `O`.
  - In `B_4` with `k = 3`, a spider has exactly one disjoint arc from `c` to `d_0`, namely `hξ_0` for
    `hδ_0`. So `ε = D^{m_{ij}}ξ_0` for each `ij ∈ O`, which gives (P1).
  - Cut along `ε` and push `D^mδ_0` off `E ∖ ε` into `Ω`.

Full proof: `h4-i25-shadow-hexagons-have-image-layer-centres-proof`.

**Machine check.** `experiments/h4-i25-image-layer-centres-2026-09-17/imglayer.py` runs on the exact constrained
`A_6` tuples of `a6.py`: curver intersection numbers, and the arc-placement region test of
`experiments/h4-pure-hexagon-z2-separation-2026-09-17/`. It tests Helly, (P1), (P2) and the existence of an
explicit image-layer centre.
- On w7-042's cabled certificate hexagon (`cert.py`), `p_c` is ejected by exactly the two pairs with `m = 0`.
  The pair with `m = 1` does not eject it, and the one vertex centre has `m = 0`, as (P1) and (P2) predict.
- The first 20 exact length-1 tuples are all in Case A, with 0 failures.

Details are in the route.

**Status.** Established (direct proof, with the machine check as a cross-check). It depends on the cited shadow
identification `h4-i25-fibred-shadows-are-rigid-cluster-braid-groups`, an unreviewed lane result. Lane w9-042,
2026-09-18.
