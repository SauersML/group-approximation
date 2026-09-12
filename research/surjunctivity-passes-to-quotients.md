---
rg: 2
id: surjunctivity-passes-to-quotients
kind: claim
title: Every quotient of a surjunctive group is surjunctive
distinct_from:
  separated-finite-normal-subgroups-preserve-surjunctivity: that is the harmless case of finite normal subgroups injecting into finite quotients; this is closure under all quotients, which is equivalent to Gottschalk's conjecture.
  finite-normal-subgroups-do-not-affect-surjunctivity: that restricts to finite normal subgroups, where the open residue is the finite residual; this allows every normal subgroup, free groups onto every group included.
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

**OPEN.** If `G` is surjunctive and `N` is a normal subgroup of `G`, then `G/N` is surjunctive.

**Equivalent to the conjecture** (Proposition E of the artifact):
- `gottschalk-via-quotient-closure`: every group is a quotient of a free group, and free groups are
  residually finite, hence surjunctive.
- `quotient-closure-from-gottschalk`: the converse direction.

The two routes form a deliberate cycle through the goal. Any positive argument that passes surjunctivity
to quotients in general proves the conjecture. Partial quotient closure is only available across finite
normal subgroups that inject into finite quotients.

## Attempts

- **Pulling an automaton back from the quotient.** An automaton over `G/N` lifts to one over `G` on
  `N`-invariant configurations only. Injectivity on the full shift over `G` is not inherited, so
  surjunctivity of `G` says nothing about the lift.
- **Table transfer.** Pushing a strict certificate forward along `G -> G/N` merges reverse products, which
  can only help surjectivity. Corollary 2 of `strict-pairs-transfer-to-table-realizations` gives the exact
  form.
