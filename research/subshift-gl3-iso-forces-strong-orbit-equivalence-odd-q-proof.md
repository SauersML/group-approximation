---
rg: 2
id: subshift-gl3-iso-forces-strong-orbit-equivalence-odd-q-proof
kind: route
title: Zel'manov's matrix ring (anti-)isomorphism followed by the K_0 strong orbit equivalence theorem
target: subshift-gl3-iso-forces-strong-orbit-equivalence-odd-q
requires:
  - subshift-gl3-iso-gives-matrix-ring-iso-odd-q
  - cantor-crossed-product-matrix-ring-iso-forces-soe
artifacts:
  - research/artifacts/sk-rigidity-ring-2026-09-13-part1.md
---

1. An isomorphism `GL_3(R_X) ≅ GL_3(R_Y)` gives `M_3(R_X) ≅ M_3(R_Y)` or `M_3(R_X) ≅ M_3(R_Y)^op`
   (`subshift-gl3-iso-gives-matrix-ring-iso-odd-q`).
2. `cantor-crossed-product-matrix-ring-iso-forces-soe`, with `m = 3`, `k = k' = F_q`, and the shifts restricted to the
   Cantor sets `X` and `Y` (infinite minimal subshifts are Cantor, since minimal and infinite gives no isolated points),
   gives strong orbit equivalence. ∎
