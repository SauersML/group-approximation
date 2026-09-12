---
rg: 2
id: free-centralizer-amalgam-inertness-proof
kind: route
title: Rewrite the amalgam as the untwisted empty-graph wreath and apply LEF graph-wreath permanence
target: free-centralizer-amalgams-are-surjunctivity-inert
requires:
  - lef-lamp-graph-wreaths-are-surjunctive
  - surjunctive-groups-carry-invisible-rigid-defects
artifacts:
  - research/artifacts/defect-window-automata-2026-09-12.md
---

Derivation (artifact Section 4).

- **Isomorphism.**
  - `Phi` sends `h` to `h` and `k` to `k_(Gamma)`. It respects the amalgamation, and
    `gamma k_Gamma gamma^-1 = k_(gamma Gamma) = k_Gamma` gives the relations of
    `Gamma x K`.
  - `Psi` sends `k_(h Gamma)` to `h k h^-1`. It is well defined because `Gamma` commutes
    with `K`. It respects the free product and the semidirect relation.
  - Both composites fix generators.
- **Surjunctivity.** `lef-lamp-graph-wreaths-are-surjunctive` applies to the empty graph
  on `H/Gamma` with no internal lamp twists. It assumes nothing about the actor.
- **Defect.** A reduced word of length two in a free product is nontrivial. The two
  sites differ because `gamma` lies outside the stabilizer `t Gamma t^-1` of `t Gamma`.
- **Invisibility for rigid pairs.** Part 1 of `surjunctive-groups-carry-invisible-rigid-defects`.
