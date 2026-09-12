---
rg: 2
id: finite-packet-payload-orientation-flow-proof
kind: route
title: Evaluate every balanced edge on the common regular multiplicity profile
target: finite-packet-flow-keeps-payload-orientation-balanced
requires:
  - finite-packet-functoriality-has-positive-regular-profile
  - finite-packet-graph-atlases-have-a-regular-stationary-flow
  - orientation-graded-mixed-returns-have-a-balanced-double
  - odd-selector-row-balances-or-kills-outer-action
---

Choose one common multiple of all packet orders and install the regular
multiplicity vector at every vertex.  Restriction, conjugacy, central cuts
and edge matching preserve it.  On the full protected regular carrier, equal
canonical trace of each balanced source/target pair gives `(FPO1)`.  Tensor
with a structural BCS tuple having a positive forbidden atom; packet and BCS
relations remain reducing and the orientation gap stays zero.

