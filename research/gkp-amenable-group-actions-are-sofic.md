---
rg: 2
id: gkp-amenable-group-actions-are-sofic
kind: claim
title: Every action of an amenable group, and every action on a finite set, is sofic (GKP Theorem 2.17 and Remark 2.18)
distinct_from:
  gkp-free-group-actions-are-sofic: that imports Theorem 2.19, for free actors; this imports Theorem 2.17 and Remark 2.18, for amenable actors and finite sets.
  gkp-sofic-action-toolkit: that imports Theorem 2.14 and Propositions 2.15-2.16; this imports the next two statements of the same section, which the toolkit node does not carry.
  amenable-action-of-a-sofic-group-need-not-be-sofic: that shows amenability of the action is not enough; this is the theorem for amenable actor groups.
---

**Literature input.** Gao--Kunnawalkam Elayavalli--Patchell, *Soficity for
group actions on sets and applications*, arXiv:2401.04945v3 = Res. Math. Sci.
12 (2025), 48.

> **Theorem 2.17.** Any action `α : G ↷ X` where `G` is an amenable group is
> sofic.
>
> **Remark 2.18.** Together with item 1 of Proposition 2.15, this implies the
> action of any group on a finite set is sofic.

Soficity of an action is GKP Definition 2.1(5).

**Where amenability of the group is used.** In the proof on page 9, `A` is a
Følner set **in the group** `G`, `φ(g)a = ga` on `A`, and the labels are
`π_s(x) = α(s^-1)x`. Such a label needs `s in G`. For a non-amenable group
with an amenable action, a Følner set of `X` gives the multiplicativity but
no such labels, and in general no labels exist
([[amenable-action-of-a-sofic-group-need-not-be-sofic]]). The stabilizer's
action is the missing ingredient ([[co-amenable-induction-of-sofic-actions]]).

DERIVATION
gkp-amenable-group-actions-are-sofic-citation
