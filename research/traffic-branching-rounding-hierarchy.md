---
rg: 2
id: traffic-branching-rounding-hierarchy
kind: claim
title: Accurate unitary tables lift to positive branching graph laws
distinct_from:
  permutation-traffic-is-simultaneous-fixed-points: that computes the graph moments of a genuine finite action and shows their limit values are already forced by word membership; this asks for the converse direction at finite defect — that an approximate unitary table admits a positive graph-functional extension near those values — which the computation neither supplies nor rules out.
  hyperlinear-implies-sofic: that is the group statement; this is a moment-realization statement about one table, in the language of graph-indexed observables, and its failure would be a concrete branching test graph with a robust deviation.
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

**Target.**  Given a unitary table with sufficiently small multiplicative
defect and regular-character trace data, construct a positive graph-indexed
functional extending its word traces — a traffic-type law — whose *connected
branching* moments are within `o(1)` of the canonical values that a finite
action would give (`permutation-traffic-is-simultaneous-fixed-points`), and
which satisfies the positivity and reflection constraints of a genuine finite
permutation traffic law.  Together with a realization step for such laws this
produces the finite action.

**Why branching observables and not word traces.**  Word traces are the
moments of directed *cycles*, and hyperlinearity already controls them.  A
test graph with a branching vertex asks something a trace cannot: whether
several matrix-entry paths can be made simultaneously compatible at a shared
vertex.  A permutation model satisfies these constraints exactly — the
spanning-tree computation shows a branching moment is a count of simultaneous
fixed points — while a diffuse unitary model has no reason to.  So the
branching moments are precisely the finite-defect data that distinguishes the
two categories before the limit, and the proposal is to use them as a rounding
hierarchy: impose consistency at ever larger test graphs until the law is
forced to be a permutation law.

**Why this is not monomialization.**  It does not ask for a basis in which
every `U_g` is almost monomial — the route that runs into common-Cartan
extraction and phase cancellation.  It asks only for a consistent family of
graph observables, which is a convex/moment problem, and the choice of basis
never appears.

**What the source dossier's own lemma costs this claim.**  At the limit there
is nothing to gain: connected branching moments of a sequence of finite actions
whose characters converge to a normal `0/1` character are forced to `0` or `1`
by word membership, so no new *asymptotic* invariant lives here.  The claim is
therefore consciously a statement about finite defect only, and its value is
that it knows its target values exactly and has only to prove quantitative
convergence to them.

## Attempts

- **Define the extension by the obvious formula and check positivity.**  The
  obvious formula — apply the graph sum to the microstate matrices — is
  well-defined but has no reason to be near the permutation values: the middle
  indices are summed coherently, so a branching vertex reads interference where
  a permutation reads a coincidence.  The gap between the two is exactly the
  quantity to be estimated, and no estimate is currently available beyond the
  trivial one.
- **Deduce the branching moments from the word traces.**  Impossible in
  general, and that is the point of the programme; recorded because a first
  draft that "reduces to cycles" has proved nothing.
- **Search for a robust obstruction instead.**  Deferred but cheap, and it is
  the recommended first experiment: enumerate connected labelled test graphs on
  3–6 vertices with at least one branching vertex (theta graphs, forks,
  diamonds, two cycles sharing a root), and maximize the deviation of the
  unitary graph polynomial from the canonical permutation value subject to
  unitarity, table and regular-trace constraints, using a symmetry-reduced
  moment relaxation.  Three outcomes are all informative: every small graph
  forced (evidence for this claim), one graph with a robust deviation (a new
  finite obstruction, feeding `finite-table-quantum-classical-hamming-gap`), or
  a deviation that vanishes only after balanced symmetric extension (direct
  evidence for `definetti-group-table-rounding`).  Directed cycles need not be
  searched at all.
