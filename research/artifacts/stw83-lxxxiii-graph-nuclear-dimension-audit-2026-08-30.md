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
reaches, such that every cycle-reachable noncyclic vertex lies downstream of a
hub.  Preload every edge emitted by a cyclic vertex and its range vertex; this
is still finite in the row-finite case.
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
is.  For a cyclic infinite emitter, one must additionally require that an old
hub reaches the emitter; this is exactly what synchronizes the noncyclic tail
beyond the finite cyclic prefix.  The condition is automatic when cyclic
vertices are finite emitters.  Under this exact extra hypothesis the old hubs
still synchronize every cycle-reachable noncyclic old or tail vertex.
Condition (K), the synchronizer property, and the finite cyclic nucleus
therefore survive, while the original graph algebra is a full corner of the
row-finite desingularized algebra.

## Remaining two-component obstruction

Evington--Ng--Sims--White, Remark 5.3, isolates two unknown entries already for
a finite graph with one nontrivial gauge-invariant ideal.  In both, the ideal is
stably circle-type.  The quotient is respectively Kirchberg-type or circle-type.
Their new theorem treats the reverse orientation, with a stable Kirchberg ideal
and a stably commutative quotient, and cannot simply be applied to the opposite
Busby extension.  The circle-crown class above stays on this favorable side and
does not solve the two minimal models.

The circle-by-circle direction now has an exact graph index computation.  Let
an upstream simple cycle feed a downstream hereditary simple cycle through a
finite acyclic connector.  Give each downstream cycle vertex weight one and
recursively give each connector vertex the sum of the weights of the ranges of
its emitted edges.  If `N` is the sum of these weights over exits from the
upstream cycle, then

```text
partial_1: K_1(circle quotient)=Z -> K_0(circle ideal)=Z
```

has absolute value `N` on a generator.  With the convention
`partial_1([u])=[P-x*x]-[P-xx*]` and the oriented cycle generator, its value is
`-N`; reversing either convention reverses the sign.  The computation lifts
the quotient generator to the sum `S` of the upstream cycle edge partial
isometries: `S*S=P` while `SS*=P-D`, and the connector recursion gives
`[D]=N` in the downstream `K_0` group.  Every genuine connector has `N>=1`.

Thus these extensions never split.  They also have no quasicentral approximate
unit of projections: compression by such projections followed by polar
correction would lift the quotient cycle unitary and force its boundary class
to vanish.  The same defect exhibits the upstream cycle projection as
infinite.  Therefore neither the stably-finite theorem nor split or
quasidiagonal-extension color reuse can settle even the minimal
circle-by-circle model.  The computation is a sharp obstruction, not a
nuclear-dimension-one theorem; the general non-Condition-(K) frontier still
requires a genuinely Toeplitz-type two-color construction for stable circle
ideals, and the circle-ideal/Kirchberg-quotient direction remains open as well.

## Canonical full-corner form of the circle-by-circle frontier

The weighted path count is not merely a `K`-theory invariant.  Choose one
vertex `v_0` on the upstream cycle and one vertex `w_0` on the downstream
cycle.  Removing these vertices breaks both cycles into paths; together with
the acyclic connector and the direction condition, the remaining finite graph
is acyclic.  Paths which start and end in `{v_0,w_0}` without an intermediate
visit to that set therefore form a finite first-return graph.

There is one first-return loop at each chosen vertex, no path from `w_0` back
to `v_0`, and exactly `N` first-return paths from `v_0` to `w_0`.  Expanding
the Cuntz--Krieger relations through the acyclic complement shows that their
path partial isometries generate the corner

```text
(p_(v_0)+p_(w_0)) C*(F) (p_(v_0)+p_(w_0)).
```

The no-exit downstream loop has full circle spectrum, so the general
Cuntz--Krieger uniqueness theorem makes the resulting map from the canonical
two-vertex graph injective.  The same acyclic expansion proves surjectivity.
The corner is full because its vertices generate both cycles and, backwards
through the connector, every remaining vertex.  Thus this is a full-corner
isomorphism, not an inference from the boundary map.

There is also a concrete model.  On the standard Hilbert `C(T)`-module, let
`S` be the unilateral shift.  The canonical `N`-exit graph algebra is

```text
C*(S^N tensor 1, K tensor C(T)) subset M(K tensor C(T)).
```

The `N` exit partial isometries are the first `N` matrix columns, the
downstream loop is the coordinate unitary in the `(0,0)` corner, and
`S^N` supplies the upstream loop with rank-`N` defect.  These elements generate
all of `K tensor C(T)`, and the no-exit-cycle uniqueness theorem again proves
faithfulness.

Consequently all finite acyclic connectors with the same `N` are stably
isomorphic and have the same nuclear dimension.  This sharply isolates the
remaining analytic task: construct a two-colour approximation for the
displayed Toeplitz-module algebra.  The ordinary Toeplitz theorem does not
apply because its ideal is `K`, whereas the canonical graph ideal here is
`K tensor C(T)`.  No dimension-one conclusion is claimed.

## A three-colour coefficient-valued Toeplitz approximation

There is now a sharper unconditional bound for the canonical family.  The
Brake--Winter proof can be followed through its quasicentral three-piece
decomposition.  Choose the approximate unit for `K tensor C(T)` by tensoring
the usual finite-rank tapered diagonal contractions with the coefficient
unit.  The cpc Toeplitz section of the quotient also has scalar coefficient.
Consequently the transition-band maps land in finite-dimensional scalar
matrix corners.  Brake--Winter's normal lift still has finite spectrum, so
their pizza-slice construction and the merging of the transition band with
the first quotient colour apply unchanged.

The difference occurs in the inner compression.  For the ordinary Toeplitz
algebra it is a matrix algebra and costs one colour.  Here it is

```text
M_r(C(T)),
```

so it has a two-colour approximation.  The second quotient colour lands in
the tail supported by `1-tilde(h)`, which is orthogonal to the inner corner
because `tilde(h)h=h`.  One inner coefficient colour can therefore be merged
with that quotient colour.  Keeping the other inner colour separate gives
three global order-zero colours and proves

```text
1 <= dim_nuc(C*(S^N tensor 1, K tensor C(T))) <= 2.
```

The lower bound comes from the `C(T)` quotient.  This improves the generic
extension estimate from three to two.  It also makes the unresolved hinge
precise: the scalar Toeplitz proof puts its whole inner corner into one colour,
whereas the coefficient circle forces two inner colours and only one is
automatically orthogonal to the transition colour.  Neither the type-I nature
of the extension nor its primitive-space topological dimension supplies a
known theorem eliminating that last colour; the literature on type-I
topological dimension explicitly leaves its exact relation with nuclear
dimension unclear in this generality.

## Plateau/buffer recolouring: exact hinge and no-go

For a fixed finite set, the coefficient-varying compact terms can be
approximated in a finite matrix corner and placed deep inside the one-plateau
of the tapered quasicentral contraction.  The scalar Toeplitz transition can
then be moved beyond a long buffer.  This geometry gives an exact sufficient
condition for dimension one.  If the two-colour approximation of the inner
compression can put one outgoing coefficient colour in the deep plateau and
the other in the full inner support, then the plateau colour is orthogonal to
the transition/first-quotient colour and the full inner colour is orthogonal
to the tail/second-quotient colour.  Pairing them produces two global colours.

There is a sharp limitation on how this condition can be proved.  Let
`D=M_r(C(T))` and split its constant unit as `p+(1-p)`, where `p` is the deep
plateau.  Suppose a two-colour approximation of the whole `D` puts its first
range in `pDp` and makes its second range block diagonal relative to `p`.
Compression to `q=1-p` kills the first colour and preserves order zero of the
second.  Such approximations would make

```text
qDq = M_s(C(T))
```

nuclear-dimensional zero, contradicting its nuclear dimension one.  Thus a
uniform block-diagonal whole-corner recolouring is impossible.  This is not a
no-go for the finite-set buffer idea itself: a successful second colour must
carry the scalar off-diagonal terms crossing the plateau boundary, while only
the coefficient-varying compact terms are localized.  Constructing that
adaptive completely positive approximation is now the exact remaining task.

## A quantitative finite-set obstruction beyond block diagonality

The off-diagonal escape above has a further necessary condition.  Let `z` be
the coordinate unitary of `C(T)`.  There is a universal `delta>0` such that

```text
norm(z-c-eta(b)) >= delta
```

for every scalar `c`, every contraction `b` in a finite-dimensional algebra,
and every cpc order-zero map `eta` from that algebra to `C(T)`.  Indeed, such
an order-zero map vanishes on noncommutative matrix summands and has the form
`sum lambda_j h_j`, where the positive functions `h_j` are pairwise
orthogonal.  If constants plus such functions converged to `z`, remove the
small arc on which `z` is close to the constant.  Its connected complement
must lie in the support of one `h_j`, forcing a punctured circle, after a
subsequence, into a single line segment.  This is impossible.

Apply this in a constant rank-one plateau corner `eM_r(C(T))e`.  Even if the
second inner colour has completely unrestricted off-diagonal terms relative
to `e`, compression shows that it cannot have scalar `e`-diagonal on the
input approximating `ze`: the first colour and that diagonal would violate
the uniform separation above.  Thus the next construction cannot merely use
the second colour as an off-diagonal carrier.  It must simultaneously encode
genuine circle variation on the plateau diagonal.  This is a finite-set
quantitative obstruction and does not assume that the second colour commutes
with the plateau projection.
