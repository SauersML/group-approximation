---
rg: 2
id: universal-binary-descent-via-affine-relay-hotels
kind: route
title: Reduce to a one-rest Hilbert hotel of odd type, certify it by an integral affine phase relay, then lift phases to the augmentation shift
target: some-nonsurjunctive-group-gives-a-binary-one
requires:
  - strict-automata-yield-odd-one-rest-hilbert-hotels
  - odd-one-rest-hilbert-hotels-carry-affine-relays
  - affine-relay-label-lifts-descend-to-two-symbols
---

Compared with `universal-binary-descent-via-death-free-rest-reduction`: that route needs a witness in which no active
input site ever becomes rest, with at most two rest symbols. This one needs one rest symbol and an odd active count.
It allows deaths, provided (i) the finite active count never drops and (ii) the phases of dying sites can be kept in
integral affine combinations nearby. Condition (i) is forced on every label-lift route by
`free-orbit-label-lifts-need-count-raising-label-automata`. So the first prerequisite is necessary for every lift
through free orbits with one fixed symbol, not just a feature of this design.

**Route.** Assume `NS_all ≠ ∅`. The first prerequisite gives a strict one-rest automaton of odd type whose count never
drops. The second gives, over some group `G'`, such an automaton with an integral affine relay. Item 3 of
`affine-relay-label-lifts-descend-to-two-symbols` gives a binary strict automaton over `G' × C_q`. So `2 ∈ NS_all`.

**How each prerequisite can fail.**
- The first fails if every strict one-rest automaton of odd type, over every group, lowers the finite count on some
  configuration. Then no label lift through free orbits with one fixed symbol and odd type descends. Binary descent
  would need witnesses whose output labels depend on relative phases.
- The second fails if count-monotone hotels exist but none carries a relay. The obstruction would then be the locality
  or algebraic invertibility of phase bookkeeping, not counting.
