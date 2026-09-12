---
rg: 2
id: rsg-kazhdan-rf-obstruction-implies-hyperbolic-rf
kind: claim
title: If Kazhdan subgroups of contracting rational similarity groups are residually finite, every hyperbolic group is residually finite
distinct_from:
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: that proves residual finiteness of Kazhdan subgroups for Rover--Nekrashevych groups, whose local maps are tree automorphisms; this shows that the same conclusion for contracting rational similarity groups would already settle Gromov's question, so it cannot be proved by that method alone.
  hyperbolic-groups-embed-in-contracting-rsgs: that imports the Belk--Bleak--Matucci--Zaremsky embedding; this combines it with Kapovich--Wise and Olshanskii to turn any residual finiteness obstruction for Kazhdan subgroups of such hosts into a proof that all hyperbolic groups are residually finite.
  non-residually-finite-hyperbolic-group: that is the open existence question itself; this is an established implication locating any counterexample inside a contracting rational similarity group as a Kazhdan group without finite quotients, and settles nothing in either direction.
artifacts:
  - research/artifacts/bh-rational-similarity-hosts-2026-09-12.md
---

**ESTABLISHED.** The proof is the route
`rsg-kazhdan-rf-obstruction-implies-hyperbolic-rf-proof`.

## Statement

If some word-hyperbolic group is not residually finite, then some contracting
rational similarity group contains an infinite word-hyperbolic group `Q` with
property (T) and no nontrivial finite quotient.

Equivalently: if every subgroup with property (T) of every contracting rational
similarity group is residually finite, then every word-hyperbolic group is
residually finite.

## What this says about Boone--Higman hosts

- The Rover--Nekrashevych obstruction
  (`kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf`) keeps
  non-residually-finite Kazhdan groups out of `V_d(H)`. Extending it to
  contracting rational similarity groups would prove that every hyperbolic group
  is residually finite. That is open (`non-residually-finite-hyperbolic-group`),
  so no argument of that shape is available for these hosts.
- In particular, excluding Deligne's lattice from contracting rational similarity
  groups needs something beyond property (T) and the failure of residual
  finiteness, such as its central `Z` or its word problem.
- This does not show that rational similarity groups host all decidable groups.
  Two established exclusions already stand:
  `complexity-bounded-host-classes-are-not-universal` and
  `decidable-fp-groups-need-not-embed-in-rational-group`.

## What this says about Gromov's question

A non-residually-finite hyperbolic group, if one exists, sits inside a contracting
rational similarity group as a Kazhdan group without finite quotients. So a
counterexample search can be run inside these hosts, and an obstruction proved
for these hosts settles the question. How the transfixing argument fails there is
recorded in the linked artifact.
