---
rg: 2
id: thompson-f-evacuation-schemes-need-capacity-three-proof
kind: route
title: A finite subgraph of density above 3.5 blocks capacity-two evacuation on the {x_0, x_1} Cayley graph of F
target: thompson-f-evacuation-schemes-need-capacity-three
requires: []
artifacts:
  - research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13.md
---

Let `Γ` be the 4-regular Cayley graph of `F` for `{x_0^(±1), x_1^(±1)}`, and let `A` be a
finite vertex set with average induced degree `δ(A)`. The directed edges from `A` to its
complement number `4|A| - δ(A)|A|`. In an evacuation scheme of capacity `C`, each path `p_v`
with `v ∈ A` is infinite and simple, so it leaves `A` along at least one of these edges, and
each edge carries at most `C` paths. Hence `|A| ≤ C(4 - δ(A))|A|`, i.e. `δ(A) ≤ 4 - 1/C`.

Guba (arXiv:2210.12304; survey arXiv:2305.07113v4, Theorem 2.8) shows that the density of
the Cayley graph for `{x_0, x_1}` is strictly greater than `3.5`: some finite `A` has
`δ(A) > 3.5`. For `C = 2`, `4 - 1/C = 3.5`, so no scheme of capacity 2 exists, and a fortiori
none of capacity 1.

Full text: `research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13.md`, §3.
