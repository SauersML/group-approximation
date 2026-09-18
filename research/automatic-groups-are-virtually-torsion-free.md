---
rg: 2
id: automatic-groups-are-virtually-torsion-free
kind: claim
title: Decide whether every automatic group has a torsion-free subgroup of finite index
distinct_from:
  hyperbolic-groups-virtually-torsion-free: that root asks the same question for hyperbolic groups, which are automatic, so a yes here answers it; a no here could come from a non-hyperbolic automatic group and would leave the root open
  automatic-groups-conjugate-finite-p-subgroups-into-a-ball: that claim bounds p-subgroup conjugacy classes; virtual torsion-freeness gives only the order bound, and it needs finite vcd as well before Brown's lemma yields the class count
  good-cocompact-proper-groups-are-virtually-torsion-free: that claim derives VTF from goodness plus a proper cocompact action; this one asks it for the whole class of automatic groups, with no goodness hypothesis
---

OPEN. Does every automatic group `G` contain a torsion-free subgroup of finite index?

**Why it matters here.** It is one of the two prerequisites of route `automatic-p-subgroup-ball-via-brown`.

**Calibration of difficulty.** Word-hyperbolic groups are automatic (ECHLPT, *Word Processing in
Groups*, Theorem 3.4.5, cited from memory and not imported into the graph). So a positive answer
would settle `hyperbolic-groups-virtually-torsion-free` positively, and this claim is at least as
hard as that root. The positive cases known to this worker come from linearity (Selberg's lemma,
for example for Coxeter groups) or from virtual specialness. None of them comes from the automatic
structure itself.

## Attempts

- 2026-09-17 (swarm-0917-w5-z-rips): opened as the torsion prerequisite of the Brown route. This
  worker found no method that runs through automatic structures.
