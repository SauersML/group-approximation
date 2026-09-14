---
rg: 2
id: invariant-output-injective-ca-need-torsion
kind: claim
title: An injective automaton with output invariant under a subgroup forces that subgroup to be finite
distinct_from:
  invariant-output-injective-automata-need-invisible-symmetry: that assumes the symmetry subgroup finite and places it in the sofic radical of the memory group; this shows finiteness is forced, so torsion-free hosts carry no invariant-output automata at all.
  full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant: that is the general constancy lemma for maps into coset shifts with infinite stabilizers; this applies it to invariant-output automata and draws the torsion-free consequence.
  invariant-output-symmetry-must-be-core-free: that forbids a nontrivial normal subgroup of the memory group inside the symmetry and is vacuous on simple memory groups; this forces the symmetry to be finite, which excludes invariant output on every torsion-free host, simple or not.
artifacts:
  - research/artifacts/fournier-facio-torsion-free-host-constraints-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

**ESTABLISHED.** Let `G` be a group, `A` a finite alphabet with `|A| >= 2`,
`H <= G` a subgroup, and `tau` an injective cellular automaton on `A^G` with

    tau(x)(gh) = tau(x)(g)       for all x, all g in G, all h in H.

Then `H` is finite.

Consequences:

- A torsion-free group carries no injective automaton whose output is invariant
  under a nontrivial subgroup. The architecture of
  `leavitt-units-carry-injective-invariant-output-automaton`, and the finite-subgroup
  corner automata of `ternary-leavitt-swap-idempotent-is-full` and
  `projective-ternary-klein-idempotent-is-full`, have no analogue on a torsion-free
  host, in particular on the Fournier--Facio group.
- Combined with `invariant-output-injective-automata-need-invisible-symmetry`, the
  symmetry of a strict invariant-output automaton is a finite subgroup lying in
  the sofic radical of the memory group.

Proof: `invariant-output-injective-ca-need-torsion-proof`.
