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

The acyclic connector itself can now be removed completely, rather than only
remembered through its index.  The theorem
`stw83-circle-connector-canonical-full-corner` chooses one vertex on each
cycle and proves that their sum is a full projection whose corner is the graph
with two loops and exactly `N` parallel edges from the upstream to the
downstream vertex.  Hence every graph in the circle-by-circle class above is
stably isomorphic to, and has the same nuclear dimension as, this canonical
graph.  It also identifies the canonical algebra concretely as

```text
C*(S^N tensor 1, K tensor C(T)) subset M(K tensor C(T)).
```

This is an explicit graph/full-corner computation, not a classification from
the six-term invariant.  It reduces the unresolved dimension-one question to
a precise Toeplitz-module family; the extra `C(T)` in the compact ideal is
exactly why the ordinary Toeplitz nuclear-dimension-one theorem does not close
the argument.  Nevertheless,
`stw83-canonical-circle-toeplitz-dimension-two-bound` adapts the
Brake--Winter construction far enough to prove

```text
1 <= dim_nuc(C*(S^N tensor 1, K tensor C(T))) <= 2.
```

The transition-band maps remain scalar and use the original Toeplitz
two-colour machinery.  A finite inner compression is `M_r(C(T))`, so its two
coefficient colours create one additional global colour.  One coefficient
colour can be merged with the orthogonal tail colour; removing the other is
the exact remaining dimension-one hinge.  The node
`stw83-plateau-buffer-recolouring-hinge` isolates a sufficient support
condition: localize one coefficient colour in a deep one-plateau, beyond the
coefficient-varying compact support and before the scalar transition band.
It also proves that one cannot obtain this by approximating the whole
`M_r(C(T))` corner block diagonally.  Such a scheme would compress to a
one-colour approximation of a nonzero matrix algebra over `C(T)`.  Any
successful two-colour proof must therefore be finite-set adaptive and use its
second inner colour to carry scalar off-diagonal terms across the plateau
boundary.  Even that transport is not sufficient if its plateau diagonal
remains coefficient-blind.  The quantitative separation theorem
`stw83-circle-unitary-order-zero-plus-constants-gap` gives a universal
`delta>0`: in a rank-one plateau corner, the circle generator cannot be
approximated within `delta` by one finite-dimensional order-zero colour plus
a constant.  This permits arbitrary off-diagonal entries in the second
colour.  Hence a successful adaptive construction must make the second
colour carry both cross-boundary matrix terms and genuinely circle-varying
information on the plateau diagonal.
