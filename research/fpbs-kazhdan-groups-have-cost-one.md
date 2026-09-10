---
rg: 2
id: fpbs-kazhdan-groups-have-cost-one
kind: claim
title: Every countably infinite group with property (T) has cost one
artifacts:
  - research/artifacts/fpbs/creative-branches.md
  - research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md
---

Hutchcroft--Pete, *Kazhdan groups have cost 1*, arXiv:1810.11015: every
countably infinite group with Kazhdan's property (T) has cost `1`, where the
cost of a group is the infimum of the costs of its essentially free
probability-measure-preserving actions. This answered a question of Gaboriau.

The statement is about the infimum, not about a common value. The paper's own
abstract adds: "It remains open if they have fixed price 1." That sentence is
the whole reason this node exists separately from
`fpbs-fixed-price-universal`: an infimal-cost-one theorem for a class supplies
one low-cost action, not equality of costs across actions, and it does not
place the class inside the fixed-price-one class that Lyons' percolation
implication needs. `fpbs-kazhdan-rankgradient-counterexample-reduction` uses
exactly this asymmetry, observing that infimum one already suffices to produce
a Fixed Price counterexample if some infinite Kazhdan group has a Farber chain
of positive rank gradient.

Property (T) is not an extra finite-generation hypothesis here: every discrete
Kazhdan group is finitely generated, recorded elsewhere in this repository as
`discrete-kazhdan-groups-are-finitely-generated`.

Status records an imported theorem, not independent mathematical verification.
