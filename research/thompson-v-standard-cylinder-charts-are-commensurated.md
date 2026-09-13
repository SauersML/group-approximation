---
rg: 2
id: thompson-v-standard-cylinder-charts-are-commensurated
kind: claim
title: "Thompson's group V commensurates the set of standard cylinder charts, with |gA Δ A| twice the caret count"
distinct_from:
  thompson-v-has-haagerup-property: that imports Farley's theorem that V is a-T-menable; this is one explicit commensurated subset with an exact caret-count formula, the construction whose failure for nV is recorded separately
---

Let `X` be the set of pairs `(U, φ)` where `U ⊆ C = {0,1}^N` is a nonempty
clopen set and `φ: C → U` is a homeomorphism in the Thompson groupoid
(piecewise prefix replacement on a finite cylinder partition). `V` acts on `X` by
`g·(U, φ) = (gU, g∘φ)`. Let `A ⊆ X` be the set of standard charts
`ι_w: u ↦ wu`, `w ∈ {0,1}^*`. Then for every `g ∈ V`,

`|gA Δ A| = 2·c(g)`,

where `c(g)` is the number of carets of the reduced tree pair of `g`. In
particular `A` is commensurated, `g ↦ |gA Δ A|` is a proper conditionally
negative definite function, and `V` has the Haagerup property.

The theorem that `V` is a-T-menable is Farley's (IMRN 2003, via a proper action
on a CAT(0) cube complex). This claim records a short direct proof by a
commensurating action. It is the construction whose failure in dimension two is
`brin-thompson-brick-charts-are-not-commensurated`.
