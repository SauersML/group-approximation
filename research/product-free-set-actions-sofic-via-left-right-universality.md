---
rg: 2
id: product-free-set-actions-sofic-via-left-right-universality
kind: route
title: If every group is left-right sofic, the Goursat reduction makes every set action of a product of free groups sofic
target: product-of-free-groups-set-actions-are-sofic
requires:
  - every-countable-group-is-left-right-sofic
  - product-free-set-actions-reduce-to-left-right-actions
---

Conditional route. It fires once
[[every-countable-group-is-left-right-sofic]] is established.

Let `F x F' ↷ X` be an action on a countable set. By GKP Propositions 2.15(2)
and 2.16 it suffices to treat each orbit `(F x F')/L`. The Goursat quotient
`Q_L` of `L` is a countable group. By the premise, every finitely generated
subgroup of `Q_L` is left-right sofic. The Theorem of
[[product-free-set-actions-reduce-to-left-right-actions]] then makes the orbit
sofic.
