---
rg: 2
id: left-right-universality-from-product-free-set-actions
kind: route
title: Left-right actions are set actions of products of free groups
target: every-countable-group-is-left-right-sofic
requires:
  - product-of-free-groups-set-actions-are-sofic
---

Conditional route. It fires once [[product-of-free-groups-set-actions-are-sofic]]
is established.

For a countable group `Q` and epimorphisms `q_1 : F ↠ Q`, `q_2 : F' ↠ Q` from
countable free groups, `(u,v).h = q_1(u) h q_2(v)^-1` is an action of
`F x F'` on the countable set `Q`. So it is sofic by the premise.
