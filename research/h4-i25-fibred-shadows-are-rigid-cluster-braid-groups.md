---
rg: 2
id: h4-i25-fibred-shadows-are-rigid-cluster-braid-groups
kind: claim
title: The three fibred I_2(5) shadows of the single-edge H_4 hexagon are rigid-cluster subgroups of P_7, so there the hexagon relation is an A_6 single-edge hexagon whose N-letters keep a 4-point pentagon cluster rigid
distinct_from:
  h4-a2-fibred-shadows-are-a4-pure-braid-retractions: that computes the A_2-flat shadows (full A_4 braid retractions, no rigidity); this computes the I_2(5)-flat shadows, where label 5 appears as a rigid 4-point cluster.
---

**Setting.** Notation is as in `h4-a2-fibred-shadows-are-a4-pure-braid-retractions` and its source
`h4-case1-pure-normal-form-and-fibred-obstruction`.
- `V = w ∩ w'` is one of the three `I_2(5)` flats with `w ∈ 𝒜_y∖𝒜_z` and `w' ∈ 𝒜_x∖𝒜_z` for which `ℓ_x`
  is modular in `ℬ_V = 𝒜_x ∪ 𝒜_y ∪ {walls ⊇ V}` (21 walls).
- The fibre points are
  - `p_1, p_2, p_3`, from the walls of `𝒜_y∖𝒜_z`; `p_c` is the one on `w`, and `p_a, p_b` are the other two;
  - `q_1, q_2, q_3`, from the three walls of `V` outside `𝒜_x ∪ 𝒜_y`.
- `𝒞'_V` (16 walls) is the 6 fibre walls together with the 10 collision walls.

**(1) Rigid cluster (the label 5).**
- The normals of `p_c, q_1, q_2, q_3` and `w'` span a plane. Hence
  `q_j(u) = p_c(u) + κ_j·s(u)`, with `s(u) = ⟨w',u⟩/⟨n_c, v_x⟩` and constants `κ_j`.
- For all three flats, up to rescaling `s`, `{0, κ_1, κ_2, κ_3} = {0, 1, φ^{-1}, φ}` (`φ` the golden
  ratio). With `∞ ↔ w'`, these
  are the 5 walls of the `I_2(5)` pencil: normals at angles `18°, 54°, 90°, 126°, 162°`.
- The 10 collision walls are:
  - `w'` alone, on which all 6 pairs of the cluster `C = {p_c, q_1, q_2, q_3}` collide at once;
  - the 3 walls of `𝒜_z`, carrying the pairs among `p_1, p_2, p_3`;
  - 6 distinct walls of `𝒜_x∖𝒜_z`, one for each pair `{p_a or p_b, q_j}`.

**(2) The shadow.**
- With `f : P_7 → P_C` forgetting `t, p_a, p_b`, and `Δ²_C` the full twist of the 4 cluster strands:
  `M(𝒞'_V) ≅ ℂ^* × Conf_3(ℂ ∖ {0, 1, φ^{-1}, φ})`, where the moving points are `t, p_a, p_b`.
- The map of the shadow lemma embeds `π_1M(𝒞'_V)` in `P_7` with image `G_V := f^{-1}(⟨Δ²_C⟩)`.
- So `ρ_V : P ↠ G_V ⊂ P_7`, and the `ℬ_V` hexagon identity holds iff `ρ_V(α_1β_1α_2β_2α_3β_3) = 1` in `P_7`.

**(3) Images.** At the base point the real order is `q_* < q_* < q_* < p_1 < p_2 < p_3 < t`. Number the
strands `1..7` in this order.
- `ρ_V|_{P_Y}` is an isomorphism onto `P_{4567}`, so `ρ_V(F) = ⟨A_{47}, A_{57}, A_{67}⟩ ≅ F`.
- `ρ_V(P_X) = G^X_V := {g ∈ P_{1…6} : g|_C ∈ ⟨Δ²_C⟩}`, where `C` is the strand set `{1,2,3, c+3}`.
- `ρ_V(N) = N_V := {g ∈ G^X_V : g|_{456} = 1}`.

**(4) Consequence.** Put `X'' = {σ_1,…,σ_5}` and `Y'' = {σ_4,σ_5,σ_6}` in `B_7`, so that `Z'' = {σ_4,σ_5}` is
of type `A_2`.
- `ρ_V` induces a type-preserving simplicial map from the single-edge layer of the `H_4` Deligne complex to that
  of the `A_6` Deligne complex for `(X'', Y'')`.
- A tuple satisfies the `ℬ_V` identity iff its image is an `A_6` single-edge hexagon, i.e.
  `α'_i ∈ F'' = ker(P_{4567} → P_{456})` and `β'_i ∈ ker(P_{1…6} → P_{456})`, with the extra condition that
  every `β'_i` lies in the rigid-cluster subgroup `N_V`.
- Every such constrained `A_6` hexagon arises.

For an `A_2` flat the cluster is `{p_c, q}`: two points, which is no constraint. That recovers the full `A_4`
retraction of the companion claim. In a single fibred shadow, label 5 enters only as the rigidity of a
4-point cluster. The shape of the cluster (the golden ratio) is invisible to `π_1`.

**What it leaves.** Among single-flat fibred shadows, the whole question is now a braid-group statement:
- Does every `A_6` single-edge hexagon with `N`-letters in `N_V` have a centre of the form `ρ_V(y_2)` or
  `ρ_V(s_4^k)A_{Y''}`?
- In the arc model, this is about arcs from puncture 7, and arcs from punctures 1–3, in a disc whose 4-point
  cluster moves only by full twists.

Proof: `h4-i25-fibred-shadows-are-rigid-cluster-braid-groups-proof`. Computations:
`experiments/h4-case1-braid-monodromy-2026-09-17/` (`i25cluster.py`, `i25cluster.log`, `i25probe.py`). Lane
w6-042, 2026-09-18, unreviewed.
