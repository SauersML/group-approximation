---
rg: 2
id: thompson-v-surjunctive
kind: claim
title: Thompson's group V is surjunctive
root: true
distinct_from:
  thompson-v-not-sofic: that asks whether V admits sofic approximations; soficity would prove this claim by Gromov--Weiss, and a strict automaton over V would prove that one, but surjunctivity of V could hold with V nonsofic.
  leavitt-unit-group-surjunctive: that is surjunctivity of the Leavitt unit group, which contains V and would give this claim; this is the smaller group, which is not known to decide that one.
artifacts:
  - research/artifacts/thompson-v-coset-peeling-circularity-2026-09-12.md
  - research/artifacts/surjunctivity-permanence-envelope-2026-09-12.md
---

**OPEN.** For every finite alphabet `A`, every injective cellular automaton
`A^V -> A^V` over Thompson's group `V = G_(2,1)` is surjective.

*Marked `root` because it is a question in its own right, unrecorded before
2026-09-12.* A strict automaton over `V` would give a nonsofic `V`
(`thompson-v-not-sofic`) and refute Gottschalk's conjecture over the Leavitt
unit group, since `V <= R^x`.

## Attempts

- **Soficity.** If `V` is sofic, `sofic-groups-are-surjunctive` proves this.
  `thompson-v-not-sofic` is open, with no mechanism in either direction.
- **Permanence.** `V` is finitely presented, infinite and simple
  (`thompson-v-finitely-presented-infinite-simple`). By
  `gottschalk-counterexamples-lie-outside-the-permanence-closure`, it lies in the
  permanence closure of the sofic groups exactly when it is sofic. So the landed
  permanence theorems add nothing beyond the soficity question.
- **Coset peeling through the Cantor action.** Dead:
  `thompson-v-surjunctive-via-coset-peeling`. Every stabilizer group the method
  offers contains a copy of `V`.
- **Cantor-orbit encodings.** Dead in general by
  `full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant`.
- **Route through the Leavitt units.** `thompson-v-surjunctive-from-leavitt-units`
  is valid but needs the harder `leavitt-unit-group-surjunctive`.
- **What is left.** An argument over `V` itself, for automata whose memory
  generates `V`, perhaps an induction on the automaton using `V_U ~= V` on
  disjoint clopens. None is known: Section 4 of the artifact.
