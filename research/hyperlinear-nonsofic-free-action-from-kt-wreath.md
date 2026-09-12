---
rg: 2
id: hyperlinear-nonsofic-free-action-from-kt-wreath
kind: route
title: A hyperlinear Kun--Thom wreath makes the Kun--Thom free action hyperlinear and nonsofic
target: hyperlinear-nonsofic-free-action
requires:
  - hyperlinear-wreath-model
  - kt-free-action-hyperlinear-iff-wreath-hyperlinear
  - kun-thom-free-nonsofic-action
---

Let `X = ({0,1},fair)^(G/Γ) × ({0,1},fair)^G` be the free ergodic action of the
Kun--Thom Theorem E group `G`.

* `kun-thom-free-nonsofic-action`: `X` is essentially free and not sofic.
* `hyperlinear-wreath-model`: the wreath `W = (⊕_(G/Γ) Z/2) ⋊ G` is hyperlinear
  (its goal statement is Connes embeddability of `L(W)`).
* `kt-free-action-hyperlinear-iff-wreath-hyperlinear`: then `L^∞(X) ⋊ G` embeds in
  `R^ω`, i.e. `X` is a hyperlinear action.

Together, `X` is a free p.m.p. action that is hyperlinear but not sofic, and its
orbit equivalence relation is a nonsofic relation with Connes-embeddable algebra.

Live and conditional: the only open prerequisite is `hyperlinear-wreath-model`,
which is the same obstacle as the group-level separation for `W`.
