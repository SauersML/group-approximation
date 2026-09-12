---
rg: 2
id: invariant-output-symmetry-must-be-core-free
kind: claim
title: The symmetry of an injective invariant-output automaton contains no nontrivial normal subgroup of the memory group
distinct_from:
  invariant-output-injective-automata-need-invisible-symmetry: that forces the symmetry into the sofic radical of the memory group by counting; this forbids, by freeness of the shift alone, any nontrivial normal subgroup of the memory group inside the symmetry, and is vacuous on simple memory groups.
artifacts:
  - research/artifacts/simple-host-direct-attack-2026-09-12.md
---

Let `tau` be an injective automaton over `G` with `tau(x)(gh) = tau(x)(g)` for all configurations
`x`, all `g`, and all `h in H <= G`.

- `H` contains no nontrivial normal subgroup of `G`.
- If the memory generates `Gamma` and `H <= Gamma`, then `H` contains no nontrivial normal subgroup
  of `Gamma`.

In particular the symmetry `H` of an invariant-output design (`leavitt-units-carry-injective-invariant-output-automaton`) cannot be central in the effective memory group. This is a design filter. It is vacuous when the effective memory group is infinite and simple.

Proposition 4 of the artifact.
