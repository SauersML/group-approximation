---
rg: 2
id: acyclic-host-container-not-fp3-via-split-edge
kind: route
title: "The acyclic-host twisted rope container satisfies the split-edge hypotheses, so it is not FP_3"
target: acyclic-host-twisted-rope-container-is-never-fp3
requires:
  - split-edge-hnn-with-non-fp2-edge-is-not-fp3
---

Check the three hypotheses for `K = HNN(A; L; f_1, f_2)` with
`A = P_0 × L × G`.

1. **`L` finitely generated, not `FP_2(Q)`.** `L = F_1 *_R F_2` is generated
   by `2k` elements. `G` contains a universal group, so it is infinite, and
   `R ≠ 1`. Then `H_2(L; Q)` is infinite-dimensional (Fournier-Facio--Zaremsky,
   arXiv:2607.21727v1, Lemma 3.3, as recorded on
   `fp2-vertex-graph-of-groups-infinite-h2-edge-kills-fp3`). A group of type
   `FP_2(Q)` has finite-dimensional `H_2(-; Q)`, so `L` is not `FP_2(Q)`, and
   hence not `FP_2`.
2. **Split edge.** `r: A → L`, the projection onto the middle factor,
   satisfies `r f_2 = id_L`. Its kernel `N = P_0 × 1 × G` is finitely
   presented, hence `FP_2`, and nontrivial.
3. **`f_1` through an `FP_2` subgroup.** `f_1(L) ≤ P_0 × 1 × 1 ≅ P_0`, which
   is finitely presented.

So `split-edge-hnn-with-non-fp2-edge-is-not-fp3` applies, over `Q` as well as
over `Z`: `K_ac(G)` is not `FP_3(Q)`.
