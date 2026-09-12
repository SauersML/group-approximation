---
rg: 2
id: leavitt-zero-rokhlin-supremum-from-strict-automaton
kind: route
title: A strict automaton over the Leavitt units forces zero Rokhlin entropy for all their free actions
target: leavitt-units-have-zero-rokhlin-entropy-supremum
requires: [leavitt-unit-group-nonsurjunctive, positive-rokhlin-entropy-makes-leavitt-units-surjunctive]
artifacts:
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

By part 3 of the second prerequisite, one free ergodic action of `U` with positive Rokhlin entropy
would make `U` surjunctive. The first prerequisite says `U` is not surjunctive. So every free
ergodic p.m.p. action of `U` has Rokhlin entropy zero, which is the target.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 24 of the verification
artifact). The prerequisite `leavitt-unit-group-nonsurjunctive` is open, so this route
establishes nothing yet.
