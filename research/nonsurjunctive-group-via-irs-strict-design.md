---
rg: 2
id: nonsurjunctive-group-via-irs-strict-design
kind: route
title: A strict design on an invariant random subgroup that transfers to a group refutes surjunctivity
target: some-group-is-not-surjunctive
requires:
  - some-free-group-irs-carries-a-strict-design
  - irs-strict-designs-yield-nonsurjunctive-groups
artifacts:
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
---

Counterexample program, by modus ponens.
- `some-free-group-irs-carries-a-strict-design` supplies an IRS carrying a strict design.
- `irs-strict-designs-yield-nonsurjunctive-groups` turns it into a group that is not surjunctive.

**Each prerequisite can fail on its own.**
- The first fails if the IRS strengthening of Gottschalk is true.
- The second fails if a nonatomic, non-co-sofic IRS carries a strict design while every group is
  surjunctive.

**Proved constraints.**
- A first-prerequisite witness is non-co-sofic (`co-sofic-irs-carry-no-strict-design`).
- If the witness is atomic, the second prerequisite is automatic
  (`atomic-irs-strict-designs-are-nonsurjunctive-quotients`).
