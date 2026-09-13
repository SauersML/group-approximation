---
rg: 2
id: radu-metabelian-quotient-sofic-via-edge-coset-action
kind: route
title: A sofic model of the edge coset action gives a sofic generalized wreath product containing G_2
target: radu-metabelian-quotient-is-sofic
requires:
  - radu-metabelian-quotient-embeds-in-edge-lamp-wreath
  - radu-edge-coset-action-is-sofic
  - gkp-wreath-permanence-theorem
---

Conditional route. It fires when `radu-edge-coset-action-is-sofic` is established.

1. `G_2 ↪ Z^2 wr_(Q/C_χ) Q` (`radu-metabelian-quotient-embeds-in-edge-lamp-wreath`, item 1).
2. `Q` is linear, hence residually finite and sofic. `Z^2` is sofic. If `Q ↷ Q/C_χ` is sofic, then
   Gao–Kunnawalkam Elayavalli–Patchell Theorem 3.6 (`gkp-wreath-permanence-theorem`) makes the
   wreath product sofic.
3. Subgroups of sofic groups are sofic.
