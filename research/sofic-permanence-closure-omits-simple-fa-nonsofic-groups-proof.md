---
rg: 2
id: sofic-permanence-closure-omits-simple-fa-nonsofic-groups-proof
kind: route
title: Push a simple FA subgroup through kernels, vertex stabilizers and colimit stages
target: sofic-permanence-closure-omits-simple-fa-nonsofic-groups
requires: []
artifacts:
  - research/artifacts/fixed-host-permanence-closure-obstruction-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Section 3 of the artifact gives the complete proof. It uses only standard
inputs:
- subgroups of sofic groups are sofic;
- Bass--Serre theory: vertex stabilizers of the Bass--Serre tree are conjugates
  of vertex groups, and a group with property FA acting on a tree fixes a
  vertex (Serre, *Trees*, Sections I.5--I.6);
- the graph-product splitting over a vertex star (Green 1990).

Each clause uses exactly one property of `Sigma`:
- colimits use finite presentation;
- extensions use simplicity;
- graphs of groups use FA;
- marked limits use finite presentation and simplicity.

Corollary 3.2 of the artifact checks that every landed surjunctivity
permanence construction is an instance of these operations over sofic or
residually finite kernels.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 12 of the
verification artifact). The colimit clause needs no injectivity of the
structure maps: a finite presentation lifts the embedding to one stage, and the
lift is injective because its composite is.
