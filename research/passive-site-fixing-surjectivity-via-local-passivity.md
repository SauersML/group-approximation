---
rg: 2
id: passive-site-fixing-surjectivity-via-local-passivity
kind: route
title: Take the neighbourhood to be one site, where fixing passive sites already creates no active site
target: injective-automata-fixing-passive-sites-are-surjective
requires:
  - local-passivity-preserving-injective-automata-are-surjective
artifacts:
  - research/artifacts/ideas-gottschalk-3-2026-09-14.md
---

Apply `local-passivity-preserving-injective-automata-are-surjective` with `A = C`, `W = {1}` and passive patterns
`P ⊆ C = C^W`. The constant pattern condition holds because `P` is nonempty. Then `Act(x) = { g : x(g) ∉ P }`.

- Hypothesis (1) of the target is the assumption `Φ(x)(g) = x(g)` whenever `x(g) ∈ P`.
- Hypothesis (2) follows from (1): if `g ∉ Act(x)` then `x(g) ∈ P` and `Φ(x)(g) = x(g) ∈ P`, so `g ∉ Act(Φ(x))`.
  Hence `Act(Φ(x)) ⊆ Act(x)`.

So `Φ` is surjective.
