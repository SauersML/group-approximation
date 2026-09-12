---
rg: 2
id: native-hecke-graph-permanence-audit-proof
kind: route
title: Apply graph-wreath sofic permanence and check the stabilizer hypothesis
target: native-hecke-graph-action-is-the-permanence-firewall
requires:
  - native-sl3-group-is-hecke-graph-wreath-product
---

By the graph-wreath identification, `G_cc` is the graph product of copies of
`C_2` over `Theta_h`, semidirect by `A`.  Theorem 1.12 of arXiv:2408.15470
applies whenever the graph action is sofic, proving `(SPF1)`.

The same paper's Theorem 1.7 automatically proves a transitive graph action
sofic when its stabilizer is amenable.  The stabilizer of the distinguished
vertex is exactly `C`, which contains nonabelian free subgroups and has
property (T), so it is not amenable.  Hence that theorem supplies no model.
The paper does not assert that every action of a sofic group on a graph is
sofic.  This leaves the arithmetic action itself as the exact permanence
firewall.
