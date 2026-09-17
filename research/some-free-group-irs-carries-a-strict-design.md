---
rg: 2
id: some-free-group-irs-carries-a-strict-design
kind: claim
title: Some invariant random subgroup of a free group carries a strict automaton design
distinct_from:
  some-group-is-not-surjunctive: that asks for a group carrying an injective non-surjective automaton; this asks only for a unimodular random Schreier graph carrying one, which kills mass-transport arguments without deciding the goal.
  end-fixing-tree-symmetries-carry-strict-automata: that calibration uses a non-unimodular transitive space; a witness here must be unimodular, since invariant random subgroups give unimodular networks.
  leavitt-unit-group-nonsurjunctive: that seeks a counterexample group; this seeks a random coset space, and on IRS-rigid hosts such as the binary Leavitt unit group the IRS statement adds nothing.
artifacts:
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
---

**OPEN (counterexample program).** Exhibit `r`, an IRS `mu` of `F_r`, and a design `D` of
shape-dependent automata with `eps_D(mu) = 0 < delta_D(mu)`. Artifact Section 2.

**Constraints already proved.**
- **Must be non-co-sofic.** `co-sofic-irs-carry-no-strict-design`. So no finite search produces a
  witness.
- **Atomic witnesses decide the goal.** A witness with an atom yields a non-surjunctive group
  (`atomic-irs-strict-designs-are-nonsurjunctive-quotients`).
- **IRS-rigid hosts give nothing new.** On quotients `F_r/N` with only trivial IRS, such as the binary
  Leavitt unit group (`leavitt-invariant-random-subgroups-are-trivial-mixtures`), the IRS containing `N`
  give no witness unless the quotient is already non-surjunctive.

**Payoff.**
- A witness refutes `free-group-irs-carry-no-strict-design`.
- It rules out every argument that uses only root-ball statistics and the mass-transport principle.
- With `irs-strict-designs-yield-nonsurjunctive-groups` it refutes the goal.

## Attempts

- **Word-rule search on subgroups (a-gs-heretic, 2026-09-17, deferred).** For constant word rules the
  forward table at a site is the coset table of its stabilizer. A witness is a conjugation-invariant law
  on subgroups whose conjugates all have forward-sufficient coset tables, while some conjugate has a
  reverse-insufficient one. Unlike over groups, forward relations generate only a subgroup, so the
  canonical table group does not bound the search. The attack is deferred: the only known non-co-sofic
  IRS are the non-constructive non-co-hyperlinear ones (`non-cohyperlinear-irs-exists`), and they come
  with no local tables to test.
