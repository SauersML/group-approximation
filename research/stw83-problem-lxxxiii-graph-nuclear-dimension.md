---
rg: 2
id: stw83-problem-lxxxiii-graph-nuclear-dimension
kind: claim
title: Every graph C*-algebra has nuclear dimension at most one (STW Problem LXXXIII)
root: true
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
---

**Problem LXXXIII of Schafhauser--Tikuisis--White.**  Is

```text
dim_nuc(C*(E)) <= 1
```

for every directed graph `E`?

The general problem remains open after a literature check through 2026-08-30.
The statements below record two unconditional parts of the frontier that are not
part of the finite-graph list in the problem statement: all stably finite graph
C*-algebras have nuclear dimension at most one, and every countable graph with
Condition (K) whose cycles pairwise meet has nuclear dimension at most one.

## Attempts

The finite-combinatorial reduction must use completed finite subgraphs, not naive
induced subgraphs.  For countable row-finite graphs with Condition (K),
`stw83-condition-k-finite-completion-reduction` gives finite Condition-(K)
approximants with injective canonical connecting maps.  Nuclear dimension at most
one then survives because the bound is uniform along the inductive system.

Faurot--Schafhauser's finite theorem has a source dichotomy: every source must
connect either to every cycle or to no cycle.  Pairwise intersection of cycles is
hereditary to finite subgraphs and forces exactly this dichotomy, yielding
`stw83-pairwise-intersecting-cycles-dimension-one`.  The proof also audits
desingularization, so infinite emitters and sinks are allowed.

The generic extension estimate does not close the problem.  For a finite
Condition-(K) graph, the standard gauge-invariant ideal decomposition gives an AF
ideal and an O-infinity-stable quotient, but the general extension inequality only
gives the upper bound two.  The improvement to one is known when the AF ideal is
stable and the extension is full; neither property is automatic for an arbitrary
finite graph.  Outside Condition (K), circle-algebra subquotients also remain in
the finite extension core.
