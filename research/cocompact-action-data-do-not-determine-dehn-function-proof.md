---
rg: 2
id: cocompact-action-data-do-not-determine-dehn-function-proof
kind: route
title: "F_2 x Z and F_2 * Z act on trees with identical action data but have Dehn functions n^2 and n"
target: cocompact-action-data-do-not-determine-dehn-function
requires: []
---

Direct proof, written in full in the claim body.

1. `G_1 = F_2 × ℤ` and `G_2 = F_2 * ℤ` are HNN extensions of `F_2`, with
   `t` centralizing `F_2` and with trivial associated subgroups respectively.
   Bass–Serre theory gives cocompact actions on trees without inversions; the
   stabilizers are conjugates of `F_2` (vertices, both groups) and `F_2`
   (edges of `G_1`) or trivial (edges of `G_2`).
2. Trees have Dehn function 0. All stabilizers are free of finite rank, so
   their Dehn functions are `≃ n`. `F_2` is a retract of both groups, so all
   stabilizers are undistorted.
3. `δ_{F_2 × ℤ} ≃ n²`: `≼` from the proper cocompact action on the CAT(0)
   space (tree × line); `≽` because `ℤ² = ⟨x, t⟩` is a retract and retracts
   have smaller Dehn functions (Alonso, *Inégalités isopérimétriques et
   quasi-isométries*, C. R. Acad. Sci. Paris 311 (1990)).
4. `δ_{F_2 * ℤ} ≃ n` because `F_2 * ℤ` is free of rank 3.

The calibration `ℤ²` versus `BS(1,2)` in the claim body uses only the
standard facts `δ_{ℤ²} ≃ n²` and `δ_{BS(1,2)} ≃ 2^n` (Epstein et al.,
*Word processing in groups*, 1992, Section 7.4) and that `⟨a⟩` is
exponentially distorted in `BS(1,2)`, since `t^n a t^(-n) = a^(2^n)`.
