---
rg: 2
id: baumslag-gersten-graph-host-obstruction-proof
kind: route
title: The image of a is conjugate to its square in A(E), hence equicontinuous on the graph path space, hence trivial
target: baumslag-gersten-embeds-in-no-graph-almost-automorphism-group
requires:
  - graph-path-almost-automorphism-proper-power-is-equicontinuous
  - baumslag-gersten-equicontinuous-generator-acts-trivially
artifacts:
  - research/artifacts/bh-bg-similarity-hosts-2026-09-12.md
---

**Item 1 (equicontinuity).** Put `g = φ(a)` and `f = φ(b)`. In `BG`,
`b a b^-1 = a^2`, so `f g f^-1 = g^2`, and `|1| ≠ |2|`. By
`graph-path-almost-automorphism-proper-power-is-equicontinuous`, `<g>` is
equicontinuous on `X_E`.

**Item 2 (triviality).** `X_E` is compact, zero-dimensional and metrizable.
`BG` acts on it through `φ`, and `a` acts by `g`. By
`baumslag-gersten-equicontinuous-generator-acts-trivially`, `g = 1`.

**Item 3 (hosts).** A topological full group of the one-sided shift of finite
type `X_E` consists of elements of `A(E)` with identity sections. `a` has
infinite order in `BG`, since `BS(1,2) = < a, b >` is a subgroup. So no
homomorphism into any subgroup of `A(E)` is injective.
