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
The statements below record unconditional parts of the frontier that go beyond
the finite-graph list in the problem statement.  They include all stably finite
graph C*-algebras, countable Condition-(K) graphs whose cycles pairwise meet, a
larger fixed-recurrent-core class on the AF-by-O-infinity side, and a countable
non-Condition-(K) class built from simple circle crowns over one Kirchberg core.
They now also include arbitrary countable Condition-(K) graphs whose recurrence
is confined to a finite cyclic nucleus and whose cycle-reachable region lies
downstream of finitely many hubs reached by every cycle (away from the cyclic
vertices themselves).

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

For a row-finite graph with a finite hereditary exhaustion, no Condition-(K)
hypothesis is needed to pass a uniform dimension-one estimate from the finite
stages; see `stw83-hereditary-finite-exhaustion-preserves-one`.  Applying this to
simple cycles feeding through finite acyclic connectors into one fixed finite
Kirchberg core gives the genuinely non-Condition-(K), non-stably-finite class
`stw83-kirchberg-core-circle-crowns-dimension-one`.

On the AF-by-O-infinity side, keeping an entire finite strongly connected core in
every hereditary finite stage makes global reachability usable: each new acyclic
feeder source reaches every cycle through the frozen core.  This yields
`stw83-finite-recurrent-core-af-feeders-dimension-one`, even when cycles in the
core do not intersect pairwise.

The strongly connected core is not essential for a different finite-completion
argument.  Suppose every cyclic vertex and cyclic edge lies in a finite nucleus
and finitely many downstream hubs are each reached by every cycle and together
reach every cycle-reachable noncyclic vertex.  Preload every edge emitted by a
cyclic vertex and its range, then retain the fixed cycle-to-hub paths and finite
hub-to-stage paths before entrance completion.  Every intermediate vertex and
every newly added sink then inherits the finite dichotomy, so all finite
approximants have nuclear dimension at most one.  This is
`stw83-finite-cycle-synchronizer-dimension-one`.  Ordering cyclic edges first
in a Drinen--Tomforde desingularization proves
`stw83-arbitrary-cycle-synchronizer-dimension-one`, so sinks and infinite
emitters are included without an extension loss, provided each cyclic infinite
emitter is itself hub-reachable so its new tail is synchronized.  The finite
hubs cannot be dropped from this proof: ambient all-or-none reachability alone
need not give a finite witness-closed completion.

The generic extension estimate does not close the problem.  For a finite
Condition-(K) graph, the standard gauge-invariant ideal decomposition gives an AF
ideal and an O-infinity-stable quotient, but the general extension inequality only
gives the upper bound two.  The improvement to one is known when the AF ideal is
stable and the extension is full; neither property is automatic for an arbitrary
finite graph.  Outside Condition (K), circle-algebra subquotients also remain in
the finite extension core.  In particular, the circle-ideal/Kirchberg-quotient
and circle-ideal/circle-quotient directions in
`stw83-two-non-k-extension-directions-remain-open` are not covered by the new
circle-crown theorem, whose Kirchberg algebra is on the ideal side.

The circle-by-circle obstruction is now sharper than this orientation warning.
For every finite graph made from an upstream simple cycle, a downstream
hereditary simple cycle, and an arbitrary finite acyclic connector,
`stw83-circle-circle-boundary-index` computes

```text
partial_1: K_1(circle quotient) -> K_0(circle ideal),
|partial_1(1)|=N,
```

where `N>=1` is the total directed path multiplicity through the connector.
The computation uses the defect projection of the lifted upstream cycle
unitary.  Consequently every genuine extension in this family is nonsplit,
has an infinite upstream cycle projection, and has no quasicentral approximate
unit of projections for the circle ideal.  This does not compute nuclear
dimension, but it rules out the two most elementary color-reuse mechanisms
for all minimal circle-by-circle models at once.
