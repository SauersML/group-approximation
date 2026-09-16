---
rg: 2
id: free-products-of-sofic-actions-are-sofic
kind: claim
title: An action of a countable free product is sofic when its restriction to every free factor is sofic
distinct_from:
  gkp-free-group-actions-are-sofic: that imports GKP Theorem 2.19 for free actors; this is permanence for an arbitrary action of an arbitrary countable free product whose factor restrictions are sofic, and it recovers Theorem 2.19 from Theorem 2.17 because a countable free group is a free product of copies of Z
  commuting-sofic-actions-need-not-combine: that answers GKP Question 4.2 (commuting actions of a direct sum) negatively; this answers the companion Question 4.3 (free products) positively
  product-of-free-groups-set-actions-are-sofic: that is the open direct-product case F x F'; the label matching here runs along the syllables of free-product normal forms and gives nothing for commuting factors
  paunescu-sofic-action-class-permanence: that is Paunescu's class of groups all of whose p.m.p. actions are sofic, closed under amalgams over amenable groups; this is the set-action notion of GKP Definition 2.1(5), and no implication from the p.m.p. notion to it is known (GKP Proposition 4.1 goes the other way)
  sofic-coset-action-makes-amalgam-double-sofic: that turns one sofic coset action into soficity of a group double; this is permanence of the action notion itself under free products of actors
artifacts:
  - research/artifacts/free-products-of-sofic-actions-2026-09-16.md
---

**Theorem (positive answer to GKP Question 4.3).** Let `G = *_(i in I) G_i`
be a free product of countable groups over a countable index set `I`. Let
`alpha : G ↷ X` be an action on a countable set. If every restriction
`alpha_i = alpha|_(G_i)` is a sofic action, then `alpha` is sofic.

Soficity of an action is GKP Definition 2.1(5): for all finite `F <= G`,
`E <= X` and `epsilon > 0` there is a unital, `(F, epsilon)`-multiplicative
`phi : G -> Sym(A)` that is an `(F, E, epsilon)`-orbit approximation of `alpha`.
No soficity of the groups `G_i` is assumed.

Gao--Kunnawalkam Elayavalli--Patchell, arXiv:2401.04945v3 = Res. Math. Sci.
12 (2025) 48, ask in their Section 4:

> **Question 4.3.** Suppose we have actions `α_i : G_i ↷ X` where `i` ranges
> over a countable index set. Then the actions naturally give rise to an
> action `α : ∗_i G_i ↷ X`. `α` is sofic iff all `α_i` are sofic?

They note that the forward direction is Proposition 2.15(3). This claim is
the reverse direction, so the answer to Question 4.3 is **yes**.

**Mechanism.** Take factor models for a common finite orbit packet. Multiply
each model by a large randomizing coordinate. This makes every labelling of
the packet occur equally often among the good points of each factor. Match
equal labels across factors with bijections. Then define `phi` on a reduced
word as the product of the conjugated factor models along its syllables. The
matched labels can be chained syllable by syllable. The full argument, with
the epsilon bookkeeping, is in the route.

**Consequences are recorded elsewhere.** Consequences that use further
imported theorems are recorded in
[[all-actions-sofic-groups-closed-under-free-products]] and
[[doubles-of-free-products-of-amenable-groups-are-sofic]]. One example is
that every action of a countable free product of amenable groups is sofic,
which recovers GKP Theorem 2.19 from Theorem 2.17. The theorem above uses no
imported input.

**Status of novelty.** On 2026-09-16 a priority search was limited to
arXiv:2408.15470, arXiv:2402.17150, arXiv:2601.18742, the abstract of
arXiv:2608.06222, and arxiv.org listing searches. None of these resolves
Question 4.3. This is not an exhaustive search.

DERIVATION
free-products-of-sofic-actions-are-sofic-proof
