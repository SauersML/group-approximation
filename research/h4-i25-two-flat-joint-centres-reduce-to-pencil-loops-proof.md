---
rg: 2
id: h4-i25-two-flat-joint-centres-reduce-to-pencil-loops-proof
kind: route
title: Semidirect centre criterion, Goursat and the pullback fibration give the two-flat joint-centre reduction to pencil loops
target: h4-i25-two-flat-joint-centres-reduce-to-pencil-loops
requires:
  - h4-case1-pure-normal-form-and-fibred-obstruction
  - h4-i25-fibred-shadows-are-rigid-cluster-braid-groups
  - h4-i25-shadow-hexagons-have-image-layer-centres
artifacts:
  - experiments/h4-two-flat-joint-certificate-2026-09-17/common.py
  - experiments/h4-two-flat-joint-certificate-2026-09-17/common.log
  - experiments/h4-two-flat-joint-certificate-2026-09-17/twocluster.py
  - experiments/h4-two-flat-joint-certificate-2026-09-17/twocluster.log
  - experiments/h4-two-flat-joint-certificate-2026-09-17/imglayer_all.py
  - experiments/h4-two-flat-joint-certificate-2026-09-17/imglayer_all.log
  - experiments/h4-two-flat-joint-certificate-2026-09-17/tuples_L111.txt
---

Notation is as in the target.

## 0. Pure centres can be taken in `P_X`

- `P_Y = F ⋊ P_Z` and `P_Z ≤ P_X`, so `P_XP_Y = P_XP_ZF = P_XF`.
- If `u = bφ` with `b ∈ P_X` and `φ ∈ F ≤ P_Y`, then `uA_Y = bA_Y`. So a pure centre, or a joint centre, may
  be taken as `b ∈ P_X`.
- Conversely, right multiplication by `F` preserves each shadow centre condition below, because
  `ρ(F) = F_Y` and `F_Y·F_Y·B = F_Y·B`.
- So joint centres are exactly the elements `b ∈ P_X` whose two images are centres.

## 1. Proof of (★)

- In `G = F_k ⋊ B`, `ρ(P_XP_Y) = B·F_Y`, and `u ∈ ρ(g_i)B F_Y` iff `u^{-1}ρ(g_i) ∈ F_Y B`.
- Take `u = c ∈ B`, and write `a_i = ρ(g_i)`.
  - `i=1`: `c^{-1} ∈ B ⊆ F_YB`. This always holds.
  - `i=2`: `c^{-1}ρ(α_1) = (c^{-1}ρ(α_1)c)·c^{-1}`, where the first factor lies in `F_k` because
    `F_k ⊲ G`. By uniqueness of the semidirect decomposition `G = F_k·B`, this lies in `F_YB` iff
    `c^{-1}ρ(α_1)c ∈ F_Y`.
  - `i=3`: `g_3 = α_1·(β_1α_2β_1^{-1})·β_1`, with `ρ(β_1) ∈ B`. So
    `c^{-1}a_3 = c^{-1}ρ(α_1)ρ(β_1α_2β_1^{-1})c · c^{-1}ρ(β_1)`. The first factor lies in `F_k`, since
    `ρ(α_2) ∈ F_k` and `F_k` is normal. Given `i=2`, the condition is `c^{-1}ρ(β_1α_2β_1^{-1})c ∈ F_Y`.
- **Invariance.** `P_Z` normalises `F` in `P_Y = F ⋊ P_Z`, so `ρ(z)` normalises `F_Y` for `z ∈ P_Z`. Hence
  `(cρ(z))F_Y(cρ(z))^{-1} = cF_Yc^{-1}`, and `Sol·ρ(P_Z) = Sol`.
- **Agreement with the `A_6` complex.** In `P_7 = F_6 ⋊ P_{1…6}` (the `t`-loops are `F_6`):
  - `P_{4567} = F''⋊P_{456}` with `F'' = ⟨A_{47},A_{57},A_{67}⟩`, so `P_{4567}P_{1…6} = F''·P_{1…6}`.
  - An element `φc` (`φ ∈ F_6`, `c ∈ P_{1…6}`) lies in `G_a` iff `c ∈ B_a`, because the forgetful map `f`
    kills `F_6`.
  - Hence `P_{4567}P_{1…6} ∩ G_a = F''·B_a = F^{(a)}_Y·B_a`. So for `u, ρ_a(g_i) ∈ G_a`, the `A_6` adjacency
    condition coincides with the condition inside `G_a`.

## 2. Proof of (J)

**Kernels.** Removing hyperplanes induces a surjection `π_1M(𝒜) → π_1M(ℬ)` for `ℬ ⊆ 𝒜`, whose kernel is the
normal closure of the meridians of `𝒜 ∖ ℬ`. (This is the standard codimension-2 argument: `M(ℬ)∖M(𝒜)` is a
union of hypersurfaces, and a generic loop or homotopy in `M(ℬ)` meets them transversally.)

**`ρ_a` on `P_X`.**
- The projection along `ℓ_x`, `M(𝒞'_a) → M(base_a)/ℓ_x`, is compatible with `M(𝒜_x) → M(base_a)`.
- `ρ_a(P_X) = B_a` is the section: the `F_6`-coordinate vanishes, by (3) of
  `h4-i25-fibred-shadows-are-rigid-cluster-braid-groups`.
- So `ρ_a|_{P_X} = ι^x_a ∘ ρ_X|_{P_X} = ι^x_a`, where `ι^x_a : P_X = π_1M(𝒜_x) → π_1M(base_a)` is induced by
  inclusion.
- Hence `K_a := ker(ρ_a|P_X)` is the normal closure in `P_X` of the meridians of `𝒜_x ∖ base_a`.
- Then `K_aK_b` is the normal closure of the meridians of `𝒜_x ∖ (base_a ∩ base_b)`. So
  `P_X/(K_aK_b) = B_{ab}`.

**Goursat.** For any group `H` with surjections `H ↠ H_1, H_2` and kernels `K_1, K_2`, the image of `H` in
`H_1 × H_2` is `{(h_1,h_2) : h̄_1 = h̄_2 in H/(K_1K_2)}`.
- Proof of `⊇`: if `h_1 = [h]`, `h_2 = [h']` and `h' = hk_1k_2`, then `hk_1` maps to `(h_1, h_2)`.
- Applied to `H = P_X` this gives `B_a ×_{B_{ab}} B_b`. Applied to `H = P`, with the kernels of `ρ_a, ρ_b`,
  it gives the fibre product over `π_1M(𝒞'_a ∩ 𝒞'_b)`.

**Joint centres.** By §0 a joint centre is `b ∈ P_X` with `ρ_a(b) ∈ Sol_a` and `ρ_b(b) ∈ Sol_b`. By
Goursat, such a `b` exists iff some `(c,c') ∈ Sol_a × Sol_b` has `ι_a(c) = ι_b(c')`. The `P_Z` version
follows from the invariance in §1, since `ι_a ρ_a = ι_b ρ_b = ρ_{ab}` on `P_Z`.

## 3. Proof of (Π)

**Walls.** `common.log` lists `𝒞'_a` and the intersections.
- `𝒞'_0 ∩ 𝒞'_1 ∩ 𝒞'_2` is `{o14, p1, p2, p3, x0, x1, x4, z0, z1, z2}`. This is 4 fibre points and their 6
  pairwise collisions: `x0 = (p1,o14)`, `x1 = (p2,o14)`, `x4 = (p3,o14)`, and `z0, z1, z2` among the `p`'s.
  So it is the `A_4` braid core, with base the braid arrangement `𝒜_3(o14,p_1,p_2,p_3)`.
- Each pair adds 2 fibre points (dropped in the base) and the 2 collision walls `{ε,ε'}` stated in the target.

**Dictionary.** `twocluster.log` resolves each collision wall into the fibre-point pairs colliding on it. By
(1) of `h4-i25-fibred-shadows-are-rigid-cluster-braid-groups`, the only walls on which a non-cluster `p`
collides with a cluster point are the 6 walls of `𝒜_x∖𝒜_z` of type `{p_a or p_b, q_j}`.
- In `V_0`, the cluster is `{p1,o13,o14,o56}`, with cluster wall `x0`. The walls meeting `p_2` are `x1`
  (with `o14`), `x2` (with `o13`) and `x3` (with `o56`); those meeting `p_3` are `x4, x5, x11`.
- In `V_1`, the cluster is `{p2,o12,o14,o37}`, with cluster wall `x1`. The walls meeting `p_1` are
  `x0, x2 (o37), x3 (o12)`; those meeting `p_3` are `x4, x6, x10`.
- So `x2, x3` are the collisions of `p_2` with `C_0∖{o14,p1}` and of `p_1` with `C_1∖{o14,p2}`. The pairs
  `(V_0,V_2)` and `(V_1,V_2)` are identical after relabelling (`common.log`).

**Linear forms.**
- In `V_a` the cluster points are `p_{a+1} + κ_j s`, where `s` is proportional to the cluster-wall form
  `p_{a+1} − o14` (fibred-shadows claim (1)). So `ε, ε'` are linear forms in `u = p_{a+1}−o14` and
  `v = p_{b+1}−o14` alone, and they do not involve `p_e`.
- The 5 walls `u=0`, `v=0`, `u=v`, `ε`, `ε'` are thus 5 distinct lines through `0` in the `(u,v)`-plane.
  They are pairwise distinct walls of `𝒜_x`.
- In the ratio `r = v/u`, they are `r = ∞, 0, 1`, and the two values `r = κ, κ'` at which `p_{b+1}` meets
  the other two points of `C_a`.
- Symmetrically, in `1/r = u/v` they are the points where `p_{a+1}` meets `C_b`.

**Fibration.**
- The walls of `base_{ab}` that involve `p_e` are exactly `(p_e,o14)`, `(p_e,p_{a+1})` and `(p_e,p_{b+1})`.
- So forgetting `p_e` maps `M(base_{ab})` to `M(5 lines) ⊂ ℂ²`, with fibre `ℂ ∖ {o14,p_{a+1},p_{b+1}}`. Those
  three points are distinct over the base, since the lines `u=0`, `v=0`, `u=v` are removed.
- This is the restriction of the fibre-type braid fibration `M(𝒜_3) → M(3 lines)` to the open subset
  `M(5 lines)`, so it is a pullback bundle with a section (`p_e` far away).
- Hence `B_{ab} = F_3 ⋊ Π_{ab}`, where `Π_{ab}` acts through `Π_{ab} → P_3`, which is `P_4 ×_{P_3} Π_{ab}`.
- `ℂ² ∖ 5` concurrent lines is a `ℂ^*`-bundle over `ℙ¹ ∖ 5` points, trivial because the base is open. So
  `Π_{ab} ≅ ℤ × F_4`.

## 4. Corollary

- An element of `P_4 ×_{P_3} Π_{ab}` is determined by its two coordinates. So `ι_a(c) = ι_b(c')` iff (i)
  and (ii) hold.
- The `P_4` coordinate of `ι_a` is the core base map. The core `𝒞'_0∩𝒞'_1∩𝒞'_2` is one of the `A_2`-flat
  shadows `P ↠ P_5` of `h4-a2-fibred-shadows-are-a4-pure-braid-retractions`: 4 fibre points plus `t`, with
  the full braid arrangement.
- `ι_a`, `ι_b` and `ρ_{ab}` commute with the maps to `P_4` and to `Π_{ab}`, all induced by inclusions of
  complements.
- The linking numbers with `ε` and `ε'` are homomorphisms `Π_{ab} → ℤ`. They factor through `H_1`.

## 5. Machine evidence

- `imglayer_all.py` is a chunked, resumable driver around the w9 `imglayer.py` test (`a6.py`, `arcs.py`,
  `search.py` of `experiments/h4-i25-image-layer-centres-2026-09-17/`, curver 0.5.1, realalg 0.3.7,
  `ARCS_N=7`). It runs on the 180 exact length-1 tuples, which are cached in `tuples_L111.txt`.
- Each log line is `index status dict`, where the dict records:
  - Helly `H`, (P1) and (P3);
  - whether `p_c` is in the `d_1`-region (`pc`);
  - the realised twist classes `tw` in `[−4,4]`;
  - the vertex-centre pairs `yc` and their classes `m`;
  - (P2), only when `p_c` is ejected.
- In all 180 lines, `pc = in-R` and `tw = [−4..4]`: the class is never pinned.
- **Reproduce.** Put curver and realalg on `PYTHONPATH` together with the w9 experiment directory, then run
  `python3 -c "import imglayer_all as m; m.main(0,180)"`.
