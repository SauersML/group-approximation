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
