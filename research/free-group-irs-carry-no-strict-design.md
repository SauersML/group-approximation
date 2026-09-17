---
rg: 2
id: free-group-irs-carry-no-strict-design
kind: claim
title: No invariant random subgroup of a finitely generated free group carries a strict automaton design
refuted_by:
  - some-free-group-irs-carries-a-strict-design
distinct_from:
  gottschalk-surjunctivity-conjecture: that quantifies over groups, where every site sees the same tables; this quantifies over unimodular random Schreier graphs with site-varying tables and shape-dependent rules, and contains the goal only as its atomic part.
  non-co-sofic-free-group-irs-carry-no-strict-design: that is the remaining non-co-sofic part; this is the whole statement, whose co-sofic part is proved.
  every-injective-ca-preserves-uniform-bernoulli-measure: that is a measure-preservation strengthening over one group; this changes the index set to random coset spaces and keeps the exact decoder identity.
artifacts:
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
---

**OPEN.** For every `r`, every invariant random subgroup `mu` of `F_r`, and every design `D` of
shape-dependent automata, it is not the case that `eps_D(mu) = 0 < delta_D(mu)`. The terms are defined
in artifact Section 2.

**Place in the graph.**
- **Implies the goal.** Route `gottschalk-via-irs-surjunctivity`: the atomic part is Gottschalk
  (`atomic-irs-strict-designs-are-nonsurjunctive-quotients`).
- **Co-sofic part proved.** `co-sofic-irs-carry-no-strict-design`. Route
  `irs-surjunctivity-via-co-sofic-split` leaves only `non-co-sofic-free-group-irs-carry-no-strict-design`.
- **Equivalent to the goal iff** `irs-strict-designs-yield-nonsurjunctive-groups` holds.
- **Why state it.** It denies homogeneity (assumption A2 of the artifact, Section 1) and keeps
  unimodularity (A1). An argument using only root-ball statistics and mass transport should hold here
  verbatim. So this is the statement such an argument actually proves, and
  `some-free-group-irs-carries-a-strict-design` is the test that can kill that whole class.

## Attempts

- **Quantitative closure (a-gs-heretic, 2026-09-17, proved in part).**
  - The inequality `delta_D <= C_D eps_D` holds on finite Schreier graphs and defines a closed convex
    set of IRS.
  - It therefore covers the co-sofic IRS.
  - It dies at non-co-sofic IRS. Nothing forces the inequality off finite models, and non-co-sofic IRS
    exist (`non-cohyperlinear-irs-exists`).
- **Atomic reduction (proved).** On atomic ergodic IRS the statement is the goal itself, so no argument
  restricted to atomic IRS is easier than the goal.
