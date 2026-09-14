---
rg: 2
id: normal-surjunctive-decoder-memory-forces-surjectivity
kind: claim
title: An injective automaton with a left inverse whose memory lies in a surjunctive normal subgroup is surjective
distinct_from:
  amenable-decoder-memory-forces-surjectivity: that needs the decoder's memory group to be amenable and uses the Garden of Eden theorem on it; this needs only a surjunctive normal subgroup containing the decoder memory, with no amenability, and transplants the automaton to that subgroup along coset coordinates.
  products-with-lef-factors-preserve-surjunctivity: that is a permanence theorem for a class of groups; this is a class theorem for automata over an arbitrary group, with a filter on designs as its consequence.
artifacts:
  - research/artifacts/amenable-extension-surjunctivity-transfer-2026-09-12.md
---

**ESTABLISHED** by `normal-surjunctive-decoder-memory-proof`.

**Theorem.** Let `G` be any group, `N` a surjunctive normal subgroup of `G`, and `tau`, `sigma` cellular automata over
`G` with `sigma tau = id`. If the memory of `sigma` lies in `N`, then `tau` is surjective, and so bijective. The memory
of `tau` and the quotient `G/N` are arbitrary.

**Filter.** In every strict pair the normal closure of the decoder memory is a nonsurjunctive group. So it is
nonsofic, and it lies outside the permanence closure `S*`.

**Scope.** On a simple group the normal closure is the whole group, so the theorem decides nothing on the Leavitt
unit groups or Thompson's `V`. It restricts strict designs over non-simple memory groups and table groups.

Proof: Section 2 of the linked artifact.
