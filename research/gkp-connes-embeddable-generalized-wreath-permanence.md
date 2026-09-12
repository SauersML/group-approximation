---
rg: 2
id: gkp-connes-embeddable-generalized-wreath-permanence
kind: claim
title: A generalized wreath product of a Connes-embeddable algebra over a sofic action of a hyperlinear group is Connes-embeddable
distinct_from:
  gkp-wreath-permanence-theorem: that imports Theorem 3.6 of the same paper, whose conclusion is soficity of G wr_alpha H from sofic G and H; this imports Theorem 3.8, whose conclusion is Connes embeddability, with only hyperlinearity asked of the acting group and the lamp algebra merely Connes-embeddable
  gkp-sofic-action-toolkit: that imports Theorem 2.14 and Propositions 2.15-2.16 about soficity of set actions themselves; this is the tracial permanence theorem that consumes a sofic set action as its hypothesis
artifacts:
  - research/artifacts/gkp-2401-04945-verified.md
---

**ESTABLISHED (literature import).** Gao--Kunnawalkam Elayavalli--Patchell,
*Soficity for group actions on sets and applications*, arXiv:2401.04945v3 =
*Res. Math. Sci.* **12** (2025), 48, verbatim from the v3 PDF (p. 14), as
transcribed in the linked artifact:

> **Theorem 3.8.** Let `(M,τ)` be a Connes-embeddable tracial von Neumann
> algebra, `H` be a hyperlinear group, `α : H ↷ X` be a sofic action. Then
> the generalized wreath product `M ≀_α H` is Connes-embeddable. In
> particular, if `G, H` are hyperlinear groups and `α : H ↷ X` is a sofic
> action, then the generalized wreath product `G ≀_α H` is hyperlinear.

Setting, from the same paper: `X` is a countable set, `α` is sofic in the
finitary sense of Definition 2.1(5) (no separation clause on the approximating
maps), and for groups `G ≀_α H = G^(⊕X) ⋊ H` with the restricted direct sum
(Definition 3.1, recorded in `gkp-wreath-permanence-theorem`).

This graph already quotes the theorem in prose inside `hyperlinear-wreath-model`
and `sofic-action-permanence`, where its hypothesis is refuted for the
Kun--Thom coset action. This node carries it as a claim so that a route can
consume it where the hypothesis does hold:
`kt-free-action-hyperlinear-iff-wreath-hyperlinear` applies it to the action of
the Kun--Thom wreath `W` on `G` through the quotient `W → G`.

**Trust surface.** Refereed journal article; verbatim transcription from the
v3 PDF; not formalised here.
