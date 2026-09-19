---
rg: 2
id: h4-i25-two-flat-joint-centres-reduce-to-pencil-loops
kind: claim
title: A joint centre for two I_2(5) shadows exists iff the two single-flat centre sets meet in B_0 = F_3 ⋊ π_1(ℂ² minus 5 concurrent lines), so beyond the A_4 core the two-flat certificate is one pencil-loop class
distinct_from:
  h4-i25-shadow-hexagons-have-image-layer-centres: that proves each single I_2(5) shadow has a centre ρ_V(g), g ∈ P; this asks for one g that is a centre in two shadows at once, and reduces that to a matching problem in the common quotient B_0.
  h4-fibred-braid-shadows-cannot-certify-case1-counterexamples: that kills certificates from any single fibred shadow; the joint two-flat condition is not a single-shadow condition, and this identifies exactly what it adds.
---

**Setting.** Notation is as in `h4-case1-pure-normal-form-and-fibred-obstruction` and
`h4-i25-fibred-shadows-are-rigid-cluster-braid-groups`.
- `(α_i, β_i)` is a Case 1 tuple, with `g_1 = 1`, `g_2 = α_1`, `g_3 = α_1β_1α_2`, so `x_i = g_iA_X`.
- A *pure centre* is `u ∈ P` with `u ∈ g_iP_XP_Y` for `i = 1,2,3`, i.e. `uA_Y` is a common upper bound.
- `V_0, V_1, V_2` are the three fibred `I_2(5)` flats. `V_a` has cluster point `p_{a+1}`, so its cluster is
  `C_a = {p_{a+1}, o14, q_a, q'_a}`, with `{q_0,q'_0} = {o13,o56}`, `{q_1,q'_1} = {o12,o37}` and
  `{q_2,q'_2} = {o15,o36}`. The wall names are those of `common.py`; `o14` is a cluster point of all three flats.
- `ρ_a : P ↠ G_a = π_1M(𝒞'_a) = F_6 ⋊ B_a` is the shadow map. Here `F_6` is the group of `t`-loops,
  `B_a = ρ_a(P_X) = π_1M(base_a)`, and `base_a = 𝒞'_a ∩ 𝒜_x` is the 10 collision walls.
  `F^{(a)}_Y = ρ_a(F)` is the free factor of `F_6` on the loops around `p_1, p_2, p_3`.
- A *joint centre* for `(V_a, V_b)` is `g ∈ P_XP_Y` such that `ρ_a(g)` and `ρ_b(g)` are centres of the two
  image hexagons in the `A_6` Deligne complex. Every pure centre is one, so a missing joint centre is a
  certificate that no pure centre exists.

**Theorem.**

**(★) Fibred centre criterion.** In any shadow `G = F_k ⋊ B` with `ρ(P_X) = B` and `ρ(F) = F_Y ≤ F_k`, an
element `c ∈ B` is a centre of the image hexagon iff
`ρ(α_1) ∈ cF_Yc^{-1}` and `ρ(β_1α_2β_1^{-1}) ∈ cF_Yc^{-1}`.
Write `Sol ⊆ B` for the set of such `c`. It satisfies `Sol·ρ(P_Z) = Sol`. For `G_a ⊂ P_7`, the centre
condition taken in the `A_6` complex (`u^{-1}ρ(g_i) ∈ P_{4567}P_{1…6}`) is the same condition, because
`P_{4567}P_{1…6} ∩ G_a = F^{(a)}_Y·B_a`.

**(J) Joint reduction.** Let `base_{ab} = base_a ∩ base_b` and `B_{ab} = π_1M(base_{ab})`, and let
`ι_a : B_a ↠ B_{ab}` be induced by inclusion. Then:
- `(ρ_a, ρ_b)(P_X) = B_a ×_{B_{ab}} B_b`, and more generally `(ρ_a,ρ_b)(P) = G_a ×_{π_1M(𝒞'_a∩𝒞'_b)} G_b`;
- a joint centre for `(V_a,V_b)` exists iff `ι_a(Sol_a) ∩ ι_b(Sol_b) ≠ ∅`. Equivalently, the images agree in
  `B_{ab}/ρ_{ab}(P_Z)` for some pair of solutions.

**(Π) The common base.** Let `e` be the third index, `{a+1, b+1, e} = {1,2,3}`. Then
`base_{ab} = 𝒜_3(o14, p_1, p_2, p_3) ∪ {ε, ε'}` has 8 walls.
- The first part is the 6-wall braid arrangement of the 4 points `o14, p_1, p_2, p_3`: the core `𝒞'_0 ∩ 𝒜_x`,
  where `𝒞'_0 = 𝒞'_0 ∩ 𝒞'_1 ∩ 𝒞'_2` is the `A_4` braid core.
- The extra pair is `{ε,ε'} = {x2,x3}` for `(V_0,V_1)`, `{x5,x11}` for `(V_0,V_2)`, and `{x6,x10}` for `(V_1,V_2)`.
- **Dictionary.** Each extra wall is simultaneously a collision of `p_{b+1}` with a point of `C_a`, and a
  collision of `p_{a+1}` with a point of `C_b`. For `(V_0,V_1)`:
  - `x2 = (p_2,o13)_{V_0} = (p_1,o37)_{V_1}`;
  - `x3 = (p_2,o56)_{V_0} = (p_1,o12)_{V_1}`.
- **Structure.** Forgetting `p_e` makes `M(base_{ab})` the pullback of the braid fibration
  `Conf_4 → Conf_3` along `M(5 lines) ⊂ M(3 lines)`. Hence
  `B_{ab} = F_3 ⋊ Π_{ab} = P_4 ×_{P_3} Π_{ab}`, with `Π_{ab} = π_1(ℂ² ∖ 5 concurrent lines) ≅ ℤ × F_4`.
  - The 5 lines are `p_{a+1}=o14`, `p_{b+1}=o14`, `p_{a+1}=p_{b+1}`, `ε` and `ε'`.
  - The free part is `π_1(ℙ¹ ∖ 5 points)` in the ratio `r = (p_{b+1}−o14)/(p_{a+1}−o14)`.
  - `P_4` is the pure braid group of `o14, p_1, p_2, p_3`: the base of the `A_4` core shadow.
- **Two pictures of Π.**
  - In the `V_a` picture, `Π_{ab}` is `p_{b+1}` circling the rigid 4-point cluster `C_a` (the values
    `r ∈ {0, 1, κ, κ'}`, with `∞` the cluster wall).
  - In the `V_b` picture, it is `p_{a+1}` circling `C_b`, with ratio `1/r`.

**Corollary.** A joint centre for `(V_a,V_b)` exists iff some `c ∈ Sol_a` and `c' ∈ Sol_b` have:
- (i) the same image in the `A_4` core base `P_4`;
- (ii) the same image in `Π_{ab}`: the class of the loop of `p_{b+1}` around `C_a` equals, after `r ↦ 1/r`,
  the class of the loop of `p_{a+1}` around `C_b`. The simplest invariants are the linking numbers with
  `ε` and `ε'`.

Condition (i) alone is the `A_4` (`A_2`-flat) shadow condition, and that shadow always has image-layer centres
(`h4-a2-fibred-shadows-are-a4-pure-braid-retractions` and the w8 result recorded on the target). So **the new
content of a two-flat certificate is exactly the pencil-loop matching (ii)**, a condition in `ℤ × F_4`.

**Where it can fail.** By the ejection-arc lemma (`h4-i25-shadow-hexagons-have-image-layer-centres`), the
single-flat solutions have a flexible twist class when `p_{a+1}` lies in the `d_1`-region, and a pinned
class `D^m P_{123}` when it is ejected. Plausibly, (ii) can fail only if both `p_{a+1}` is ejected in `V_a` and
`p_{b+1}` is ejected in `V_b`, with pinned classes whose `Π`-images differ. This is a heuristic, not proved:
the `Π`-image of a pinned class also depends on the `P_{123}` factor.

**Also found (machine).** Two-cluster fibred shadows exist, which corrects the target's w9 remark that
"there is no braid picture with two rigid clusters".
- For each pair `(V_a,V_b)`, take the core together with one extra cluster point from each flat. For 2 of
  the 4 choices, `ℓ_x` is modular (`twocluster.log`). This gives 6 fibred shadows `𝒟`, each with 6 fibre
  points and 10 collision walls.
- Their collision walls are:
  - two 3-point rigid clusters, e.g. `{p_1, o14, o13}` on `x0` and `{p_2, o14, o12}` on `x1`;
  - one *double* wall (`z0`: `p_1=p_2` together with `o13=o12`);
  - 7 single walls.
- They are not joint certificates: `𝒟` contains neither `𝒞'_a` nor `𝒞'_b`. They are new single shadows, with
  a coupled collision that no single-flat shadow has.

**Evidence (single flat, `imglayer_all.py`).** The w9 ejection-arc check was run on the 180 exact length-1
tuples of `tuples_L111.txt`, with `ARCS_N=7`. Results on all 180:
- every tuple is `determined`, with Helly, (P1) and (P3) holding;
- `p_c` is always in the `d_1`-region `R`, and every twist class `D^j`, `j ∈ [−4,4]`, carries a centre.

So none of these tuples is a candidate for (ii): short tuples never pin the class. A mismatch needs tuples in
which some pair region ejects `p_c`.

**Status.** Established for (★), (J), (Π) and the Corollary: direct proof in the `-proof` route. The wall
incidences come from `common.py` (exact root system, floating-point incidence with tolerance `1e-9`) and are
cross-checked by `twocluster.py`. The `𝒟` shadows are a machine computation. The failure heuristic is open.

It is open whether condition (ii) can fail on a genuine Case 1 tuple. If it fails, that tuple has no upper
bound, a counterexample to the target. If (ii) holds for all tuples, two-flat certificates are dead, like
single-flat ones.

Lane w10-042, 2026-09-18.
