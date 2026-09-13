---
rg: 2
id: baumslag-gersten-rn-obstruction-via-equicontinuity
kind: route
title: The image of a is conjugate to its square in A_{d,r}, hence equicontinuous on the Cantor space, hence trivial
target: baumslag-gersten-embeds-in-no-rover-nekrashevych-group
requires:
  - almost-automorphism-conjugate-to-proper-power-is-equicontinuous
  - baumslag-gersten-equicontinuous-generator-acts-trivially
artifacts:
  - research/artifacts/bh-bg-similarity-hosts-2026-09-12.md
---

The full proof is §6 of the artifact.

**Item 1 (equicontinuity).** Put `g = φ(a)` and `f = φ(b)`. Then
`f g f^-1 = g^2`, and `|1| ≠ |2|`. By
`almost-automorphism-conjugate-to-proper-power-is-equicontinuous`, `<g>` is
equicontinuous on `X_{d,r}`.

**Item 2 (triviality).** `X_{d,r}` is compact, zero-dimensional and
metrizable. `BG` acts on it through `φ`, and `a` acts by `g`. By
`baumslag-gersten-equicontinuous-generator-acts-trivially`, `g = 1`.

**Item 3 (hosts).**
- `V_{d,r}(G) ≤ A_{d,r}` for every self-similar `G ≤ Aut(T_d)`. Its elements
  replace prefixes and then act by elements of `G`.
- `V_{d,r} ≤ A_{d,r}`, and `F ≤ T ≤ V = V_{2,1}`.
- `a` has infinite order in `BS(1,2) ≤ BG`. So no homomorphism into any of
  these groups is injective.
