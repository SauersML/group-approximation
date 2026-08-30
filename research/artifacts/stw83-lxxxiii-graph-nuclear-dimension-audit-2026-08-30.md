# STW Problem LXXXIII: graph nuclear-dimension audit (2026-08-30)

## Status and current sources

Problem LXXXIII asks whether every graph C*-algebra has nuclear dimension at
most one.  No paper claiming a general solution was found through 2026-08-30.
The July 2026 arXiv update of Faurot--Schafhauser still proves the upper bound two
for all countable Condition-(K) graphs and the upper bound one only under its
finite source condition.  The July 2026 paper of Pask concerns higher-rank graphs
under pure-infiniteness and topological-dimension-zero hypotheses and does not
settle the directed-graph problem.

The primary sources used here are:

1. Faurot and Schafhauser,
   [Nuclear dimension of graph C*-algebras with Condition (K)](https://arxiv.org/abs/2310.15073),
   arXiv version 2, dated 28 July 2026.  Theorem A gives dimension at most two
   for countable Condition-(K) graphs.  Proposition 2.3 and Theorem 2.4 provide
   faithful finite entrance completions for countable row-finite graphs.  Theorem B
   gives dimension at most one for a finite graph when each source connects to
   every cycle or to none.

2. An Huef and Williams,
   [Nuclear dimension of groupoid C*-algebras with large abelian isotropy](https://arxiv.org/abs/2412.10241),
   arXiv version 4, dated 26 January 2026 and published in IMRN in 2025.
   Theorem 6.1 proves that every stably finite graph C*-algebra has nuclear
   dimension at most one.

3. Evington, Ng, Sims, and White,
   [Nuclear dimension of extensions of commutative C*-algebras by Kirchberg algebras](https://arxiv.org/abs/2409.12872),
   gives further dimension-one finite graph classes with stabilized circle-algebra
   quotients.  These are already discussed in the STW problem statement and are
   not relabelled as new progress here.

4. Pask,
   [Nuclear dimension, pure infiniteness and real rank for higher rank graph
   C*-algebras](https://arxiv.org/abs/2607.27691), submitted 30 July 2026.
   Its dimension-one theorem assumes pure infiniteness and primitive-space
   topological dimension zero for a row-finite locally convex higher-rank graph.
   It neither treats mixed finite/infinite directed-graph extensions nor closes
   Problem LXXXIII.

## Direct-limit audit

For countable row-finite Condition-(K) graphs, arbitrary finite subgraphs are not
enough.  A finite receiver may omit edges that occur in the ambient
Cuntz--Krieger equality, so the generator assignment need not define the desired
inclusion.  The Faurot--Schafhauser entrance completion closes the finite graph
under all edges received at an existing receiver and adds enough return paths to
retain Condition (K).  Row-finiteness makes the closure finite; Condition (K) and
nonzero vertex projections make its canonical map faithful.

Nuclear dimension satisfies

```text
dim_nuc(lim A_n) <= liminf dim_nuc(A_n),
```

so a uniform one-color bound on these completed finite graph algebras passes to
the countable graph without loss.  This step does not use an extension theorem.

## Extension-core audit

For a finite Condition-(K) graph, the standard source ideal is AF and the
no-source quotient is O-infinity-stable.  The general nuclear-dimension extension
estimate gives two, not one.  Faurot--Schafhauser obtain one only after proving
that the AF ideal is stable and that the extension is full.  Combinatorially these
facts require every relevant source to connect to every cycle.  Sources connecting
to no cycle can be removed as a finite-dimensional direct summand.  Thus an
argument that merely lists dimension-at-most-one subquotients does not prove
Problem LXXXIII; it must also solve the color-reuse problem across each extension.

Outside Condition (K), not every ideal is gauge invariant and stabilized circle
algebras occur among the finite graph subquotients.  The Condition-(K) entrance-
completion theorem therefore cannot be quoted as a reduction for arbitrary graph
algebras without an additional argument.

## New pairwise-cycle class

Suppose a countable Condition-(K) graph has the finite-hereditary property that
every two cycles share a vertex.  Every finite entrance completion retains this
property.  If a source in such a completion reaches one cycle, it can follow that
cycle to its intersection with any other cycle, and hence reaches every cycle.
The finite source theorem therefore gives nuclear dimension at most one for every
approximant, and inductive-limit permanence gives the same bound for the original
row-finite graph.

Sinks and infinite emitters do not obstruct the result.  In a Drinen--Tomforde
desingularization, a cycle using an added tail must also pass through the base
singular vertex, and collapsing its finite tail segments recovers an old cycle.
Their path bijection is Lemma 2.6 of
[The C*-algebras of arbitrary graphs](https://arxiv.org/abs/math/0009228),
Condition-(K) permanence is Lemma 2.7(b), and the full-corner statement is
Theorem 2.11.  Thus pairwise cycle intersection and Condition (K) both survive.
Winter--Zacharias, Corollary 2.8, then preserves nuclear dimension in the full-
corner passage.

The pairwise-intersection condition is doing real uniform work: global reachability
from one cycle to another would not suffice, because the connecting path need not
occur in a chosen finite entrance completion.  Intersection provides the needed
path inside the union of the two cycles already present.

## Hereditary finite exhaustions without Condition (K)

There is a simpler finite-limit bridge when a countable row-finite graph has an
increasing exhaustion by finite hereditary vertex sets.  Heredity ensures that all
edges emitted at an included vertex remain included, so its Cuntz--Krieger equality
is unchanged.  The canonical map from each finite induced graph algebra is gauge
equivariant and has nonzero vertex projections; gauge-invariant uniqueness makes
it injective.  The union contains every graph generator, and Winter--Zacharias
inductive-limit permanence passes a uniform nuclear-dimension-one bound without
adding a color.

Row-finiteness is essential in this formulation.  An infinite emitter can become
a finite regular vertex in a finite subgraph, which imposes an equality absent in
the ambient graph algebra.  One would need a relative graph or a different finite-
completion construction to cover that situation.

## New non-Condition-(K) circle-crown class

Fix a finite strongly connected graph `K` with an edge which is not a simple
cycle.  Attach countably many disjoint finite simple cycles, each with an exit
through a finite acyclic connector toward `K`; require every connector vertex to
reach `K`, with no edge from `K` back to a block and no edge between blocks.  The
first `n` blocks together with `K` form a finite hereditary stage.

At each stage, the cycles form `V_0`, the acyclic connectors form `V_1`, and `K`
forms `V_2` in Evington--Ng--Sims--White, Proposition 5.1.  The corresponding
graph algebra is an essential extension of a stably commutative finite circle sum
by a stable Kirchberg ideal.  Their Corollary 4.2 reuses both colors and gives
nuclear dimension one.  Hereditary finite exhaustion gives the same value for the
countable graph.

This class is not hidden inside either earlier broad theorem.  Each attached
simple cycle has an exit but has no second return path because no path returns
from `K`; hence Condition (K) fails.  A cycle with an exit produces an infinite
projection, so the graph algebra is not stably finite.

## A fixed-core AF-by-O-infinity class

The earlier warning that global cycle reachability need not survive a finite
completion has a useful converse.  Suppose all cycles lie in one fixed finite
strongly connected Condition-(K) core `K`, and the remaining graph is a countable
union of finite acyclic feeder blocks directed toward `K`.  Include the whole core
in every finite hereditary stage.  Every finite-stage source then reaches `K` and,
by strong connectivity, reaches every cycle.  Faurot--Schafhauser's finite theorem
applies at every stage, even when distinct cycles of `K` do not meet.  In extension
language, the AF source ideal is stable and the O-infinity quotient extension is
full at each stage, so the one-color reuse is uniform.

## New finite downstream-synchronizer class

There is a broader way to make the added-source problem in
Faurot--Schafhauser finite completions uniform.  Work first in the standard
edge convention.  Suppose all cyclic vertices and cyclic edges lie in a fixed
finite subgraph and there are finitely many downstream hubs which every cycle
reaches, such that every cycle-reachable vertex lies downstream of a hub.
Retain the finite cycle-to-hub paths once and, before each entrance completion,
retain a hub-to-vertex path for every cycle-reachable vertex already present.
Every intermediate vertex on such a path is visibly reached inside the stage
by every cycle.  The completion adds only new sinks.  Such a sink either has a
cycle-reachable predecessor, in which case all retained paths reach it, or all
its predecessors are no-cycle vertices, in which case no cycle reaches it.
Thus every finite completion satisfies the exact finite sink/source dichotomy
and has nuclear dimension at most one.

This permits several disjoint recurrent components and an arbitrary countable
acyclic network downstream of finitely many common hubs; neither pairwise cycle
intersection nor a strongly connected recurrent core is required.  The finite
hub hypothesis is essential to the proof: bare ambient all-or-none reachability
does not itself guarantee that repeatedly adjoining witnesses has a finite
fixed point.  The proof is an injective direct-limit argument, so no extension
inequality adds a color.

Sinks and infinite emitters can be retained.  In a Drinen--Tomforde
desingularization, enumerate first the finitely many emitted edges which belong
to cycles.  Collapsing tails shows that every new cycle is the lift of an old
one and is confined to a finite initial tail enlargement of `K`.  A new tail
vertex is reached by all lifted cycles exactly when its base singular vertex
is.  The old finite hubs still synchronize every cycle-reachable old or tail
vertex.  Condition (K), the synchronizer property, and the finite cyclic
nucleus therefore survive, while the original graph algebra is a full corner
of the row-finite desingularized algebra.  This proves the same one-color bound
for arbitrary countable graphs in this class.

## Remaining two-component obstruction

Evington--Ng--Sims--White, Remark 5.3, isolates two unknown entries already for
a finite graph with one nontrivial gauge-invariant ideal.  In both, the ideal is
stably circle-type.  The quotient is respectively Kirchberg-type or circle-type.
Their new theorem treats the reverse orientation, with a stable Kirchberg ideal
and a stably commutative quotient, and cannot simply be applied to the opposite
Busby extension.  The circle-crown class above stays on this favorable side and
does not solve the two minimal models.  Thus the general non-Condition-(K)
frontier still requires color reuse for stable circle ideals.
