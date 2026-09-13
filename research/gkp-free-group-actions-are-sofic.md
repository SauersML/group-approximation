---
rg: 2
id: gkp-free-group-actions-are-sofic
kind: claim
title: Every action of a countable free group on a countable set is sofic (Gao--Kunnawalkam Elayavalli--Patchell Theorem 2.19)
distinct_from:
  gkp-sofic-action-toolkit: that imports Theorem 2.14 and Propositions 2.15--2.16 of the same paper (locally finite stabilizers, restriction, orbits); this imports Theorem 2.19, the free-actor theorem, which the toolkit node does not carry
  gkp-free-generalized-wreath-soficity: that imports the free generalized wreath permanence theorem 3.7, which assumes a sofic action; this supplies the hypothesis for every free-group action
---

Let `F` be a countable free group and `α : F ↷ X` an action on a countable
set. Then `α` is a sofic action in the sense of Gao--Kunnawalkam
Elayavalli--Patchell, arXiv:2401.04945v3, Definition 2.1.

No hypothesis is placed on the stabilizers. In particular, for every
subgroup `Γ ≤ F`, the left coset action `F ↷ F/Γ` is sofic. This holds
even when `Γ` is normal and `F/Γ` is a nonsofic group, as used in
`mihailova-coset-wreath-sofic-action-boundary`.

Several routes already cite this theorem inline
(`mihailova-coset-wreath-sofic-action-boundary-proof`,
`mihailova-stabilizer-proof`, `non-ce-relation-admits-algebraic-action-envelope`).
Its statement is quoted in `research/artifacts/gkp-2401-04945-verified.md`.
No claim carried it before this node.

DERIVATION
gkp-free-group-actions-are-sofic-citation
