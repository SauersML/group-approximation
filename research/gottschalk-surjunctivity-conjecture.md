---
rg: 2
id: gottschalk-surjunctivity-conjecture
kind: claim
title: Every group is surjunctive on every finite-alphabet full shift
root: true
goal: true
refuted_by:
  - leavitt-unit-group-nonsurjunctive
distinct_from:
  gottschalk-surjunctivity-fixed-two-generator-tester: that establishes a reduction to one group; this is the universal conjecture itself, still unresolved here.
  leavitt-unit-group-nonsurjunctive: that seeks one counterexample and would refute this universal positive goal; it is not a positive proof prerequisite.
artifacts:
  - notes/GOTTSCHALK_RESEARCH_2026-09-07.md
---

For every group G and every finite nonempty alphabet A, every injective
cellular automaton tau:A^G -> A^G is surjective. An empty alphabet gives
the trivial empty configuration space and causes no additional case.

A cellular automaton means a continuous equivariant self-map of the full
shift, equivalently a map given by a finite memory set and a local rule.
The topology is the product of the discrete alphabet topologies. A proper
invariant subshift cannot replace the full shift in this statement.

This records the positive goal requested on 2026-09-07. Neither the
repository's nonsofic-group constructions nor a completed dependency
reduction settles it. Its negative Leavitt lane remains separate; a
counterexample there would refute this claim.

## Attempts

The finite-observable approach now yields the quantitative criterion
split-ca-defects-force-linear-observable-rank: a strict encoder has a
positive defect seed generating a tower of dimension n delta. It does
not furnish an upper bound contradicting that growth.
reversible-xor-has-linear-observable-rank disproves the proposed universal
sublinear bound, even for the unique decoder of a bijective automaton.
Another invariant must distinguish defect growth from reversible growth.

The fixed-test-group route below uses the existing reduction honestly:
surjunctivity of the test group itself remains an open prerequisite.
