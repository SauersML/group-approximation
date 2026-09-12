---
rg: 2
id: nonsofic-one-relator-relator-has-primitivity-rank-two-proof
kind: route
title: Exhaust the three other primitivity ranks by virtual specialness
target: nonsofic-one-relator-relator-has-primitivity-rank-two
requires: []
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

## Direct proof

Residually finite groups are sofic, so it suffices to rule out `π(w) ∈ {1, 3+, ∞}`
by residual finiteness, which the claim does case by case.  The three literature
imports, each checked on 2026-08-17 and recorded in the artifact:

- `π(w) = 1` ⟺ `w` a proper power ⟹ `G` has torsion ⟹ virtually compact
  special (**Wise**);
- `π(w) >= 3` ⟺ negative immersions (**Louder--Wilton**) ⟹ hyperbolic and
  virtually compact special (**Linton**, *One-relator hierarchies*, Duke Math.
  J. **174** (2025) no. 4, resolving the Louder--Wilton conjecture);
- `π(w) = ∞` ⟺ `w` primitive in `F` (**Puder--Parzanchevski**) ⟹ `G` free.

The consequences — torsion-freeness and local indicability — then come from the
one-relator torsion theorem and Brodskii's theorem.

`requires: []` because every input is external and none of it is stated as a
separate claim in this graph; the trust surface is the three attributions above,
not any node here.  Unlike Linton's rational-derived theorem, none of these is
load-bearing for more than this one claim, so none is worth its own import node.
