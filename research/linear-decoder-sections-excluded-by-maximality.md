---
rg: 2
id: linear-decoder-sections-excluded-by-maximality
kind: route
title: Maximal Bernoulli Rokhlin entropy excludes measurable sections of linear decoders into larger alphabets
target: linear-decoders-over-leavitt-units-admit-no-measurable-section
requires:
  - bernoulli-rokhlin-entropy-maximal-for-every-group
artifacts:
  - research/artifacts/ornstein-weiss-decoder-sections-2026-09-12.md
  - research/artifacts/measurable-alphabet-compression-2026-09-12.md
---

A section `tau` of a linear decoder `(F_p^m)^U -> (F_p^(m'))^U` with `m < m'` is injective on a conull set, because
`L o tau = id`. So its time-zero partition `{tau(x)(1) = b}` generates, and has `p^m` pieces (Proposition 1 of the
compression artifact). That gives `h^Rok_U((F_p^(m'))^U) <= m log p < m' log p`, contradicting maximality over `U`.
