---
rg: 2
id: higman-group-graph-host-obstruction-proof
kind: route
title: Each generator image is conjugate to its square in A(E), hence equicontinuous on the graph path space, and equicontinuous H4-actions on compact zero-dimensional spaces are trivial
target: higman-group-embeds-in-no-graph-almost-automorphism-group
requires:
  - graph-path-almost-automorphism-proper-power-is-equicontinuous
  - higman-group-embeds-in-no-almost-automorphism-group
artifacts:
  - research/artifacts/ideas-2026-09-13/bh/bh-ec-groups.md
---

**Item 1 (equicontinuity).** Let `φ : H4 → A(E)` and put `h_i = φ(g_i)`. The
relation `g_(i-1) g_i g_(i-1)^-1 = g_i^2` gives
`h_(i-1) h_i h_(i-1)^-1 = h_i^2`, and `|1| ≠ |2|`. By
`graph-path-almost-automorphism-proper-power-is-equicontinuous`, each `<h_i>` is
equicontinuous on `X_E`.

**Item 2 (triviality).** `X_E` is compact, zero-dimensional and metrizable. By
Item 2 of `higman-group-embeds-in-no-almost-automorphism-group`, an action of
`H4` by homeomorphisms of such a space in which every `<h_i>` is equicontinuous
is trivial. So every `h_i = 1`.
