---
rg: 2
id: brunnian-four-braids-are-pseudo-anosov
kind: claim
title: "Brun_4 is a free normal subgroup of B_4 meeting the center trivially, and every nontrivial Brunnian 4-braid is pseudo-Anosov"
artifacts:
  - research/artifacts/zp-burau-four-strand-mechanism-2026-09-13.md
---

`Brun_4 ⊂ P_4` is the group of pure 4-braids that become trivial when any one strand is deleted.

1. `Brun_4` is normal in `B_4`, meets `Z(B_4) = ⟨Δ²⟩` trivially, and is a nontrivial free group.
   Explicitly, `Brun_4 = push(∩_{i=1}^{3} ker π_i)`, where:
   - `push : π_1(D_3, p_4) → B_4` is the point-pushing map;
   - `y_1, y_2, y_3` is the free basis of loops around `p_1, p_2, p_3`;
   - `π_i` kills `y_i`.

   For example, `push([[y_1,y_2],y_3]) ≠ 1` is Brunnian.
2. Every nontrivial element of `Brun_4` is pseudo-Anosov, as a mapping class of the sphere with
   the five marked points `p_1, ..., p_4, ∞`.

Part 2 is used in arXiv:2607.05283v1 (Theorem 6.6, cited there to Whittlesey). The route
`brunnian-four-braids-are-pseudo-anosov-proof` proves both parts directly for `n = 4`.
