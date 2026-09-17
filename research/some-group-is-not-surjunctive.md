---
rg: 2
id: some-group-is-not-surjunctive
kind: claim
title: Some group carries an injective non-surjective cellular automaton on a finite-alphabet full shift
root: true
distinct_from:
  gottschalk-surjunctivity-conjecture: that is the universal positive goal; this is its negation, recorded as a program target so that counterexample routes through unnamed groups have a claim to target.
  leavitt-unit-group-nonsurjunctive: that names one candidate group; this names none and collects routes that produce a group from other data.
  some-nonsurjunctive-group-gives-a-binary-one: that converts a non-surjunctive group into one on a binary alphabet; this is the bare existence statement it starts from.
artifacts:
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
---

**OPEN.** There exist a group `G`, a finite alphabet `A`, and a cellular automaton `tau : A^G -> A^G`
that is injective and not surjective. This is the negation of `gottschalk-surjunctivity-conjecture`.
It is listed in that claim's `refuted_by`.

Every named counterexample claim in the root's `refuted_by` list implies this claim. They are not wired
as routes here. The route added with this node is `nonsurjunctive-group-via-irs-strict-design`.

## Attempts

- **Invariant random subgroups (a-gs-heretic, 2026-09-17).** It needs both
  `some-free-group-irs-carries-a-strict-design` and `irs-strict-designs-yield-nonsurjunctive-groups`.
  The first can only be met by a non-co-sofic IRS. The second has no monotone mechanism. Artifact
  Sections 5 and 6.
- **Data-routed transport (swarm-0917-w4-gs-heretic, 2026-09-17).**
  - **Rejected host-class kills.** Kills of rigidity host classes (Kazhdan, simple, intermediate) cannot
    work: non-surjunctivity passes to overgroups, so simple Kazhdan hosts carry the whole problem.
  - **Killed mechanism class** (`data-routed-automata-defeat-transport-accounting`). Every automaton is a
    data-routed copy rule. The Klein parity involution leaves 1/4 of its sites unread in every copy
    presentation, so site-transport invariants (indegree balance, collision mass, "unread implies invisible")
    say nothing beyond certificate-independent routing. This answers the site-mixing gate of
    `marker-routed-paradoxical-transport-must-collide`.
  - **Named candidate mechanism.** Blind copy automata (hypercube perfect matchings, including
    multiplexers) contain no linear rule, so they avoid Kaplansky direct finiteness. They are surjunctive at
    memory at most three. Their status at four or more addresses is open, and no construction step was
    found there.
