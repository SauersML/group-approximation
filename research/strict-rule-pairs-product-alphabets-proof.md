---
rg: 2
id: strict-rule-pairs-product-alphabets-proof
kind: route
title: Run the old code on the first coordinate and copy the label-one cell on the second
target: strict-rule-pairs-pass-to-product-alphabets
requires: []
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
---

Section 2 of the artifact.
- **`Dec`.** The first coordinate satisfies `Dec(T_f)` by the original code. The second coordinate
  copies cell `(s,1)` at each relay, and the sink reads relay `1`, so it returns `p_B(1,1)`.
- **`Enc` fails.** It fails on the first coordinate for the original witness `q_A`, paired with a
  constant `q_B`.
- **Groups.** The group corollary is `tau x id_B` with decoder `sigma x id_B`, or equivalently the
  realized tables with Corollary 1.4 of `gottschalk-rectangle-clauses-and-recognition-2026-09-12.md`.
