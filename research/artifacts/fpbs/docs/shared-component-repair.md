# Shared component repair and the missing information in a cut argument

Written research deduction, September 10, 2026. This note constructs
arbitrarily cheap repairs under an explicit component-contact hypothesis.
It also tests a possible route to that hypothesis from relative cycle
operators. It does not prove Fixed Price, claim mathematical priority,
or claim formal or independent verification.

## 1. Infinite contacts give zero relative cost on the original action

Let R be the orbit relation of a free p.m.p. action of a countably
infinite group on (X,mu). Let H be a simple generating graphing of
finite cost h, represented by oriented restrictions g_j|D_j, each
unoriented edge represented once. Finite cost makes H locally finite
on an invariant conull set. Let S be any measurable subrelation of R.

In each R-orbit form a graph whose vertices are the S-classes. Join
two distinct classes when infinitely many H-edges have one endpoint
in each class. Assume this graph is connected in almost every orbit;
a single vertex counts as connected. Then

    relC(R;S)=0.                                          (1)

Here relative cost is the infimum of c(A) over graphings A with
S join R_A=R. The construction takes place on X itself. It does not
assume an equivariant selector of the S-classes or that a random
extension preserves relative cost.

First, independently mark each vertex of an orbit with probability
epsilon>0 and retain each H-edge whose oriented starting point is
marked. Infinitely many H-edges between a fixed pair of S-classes
have infinitely many distinct starting vertices, by local finiteness.
Almost surely at least one of these vertices is marked. There are
only countably many pairs of classes in an orbit. Thus all the
infinite contacts are joined simultaneously almost surely, and
the retained edges together with S connect the orbit. Their expected
graphing cost is epsilon h.

This random construction alone would live on an extension. The
following finite approximation returns the repair to X.

Fix eta>0 and choose a finite prefix of H whose remaining cost is
below eta/3. These finitely many partial maps are the demands to
be tested. In the random construction each demand is connected by
a finite path consisting of S-steps and retained H-steps almost
surely. Enumerate S by the restrictions

    g|{x:(x,g.x) in S},   g in Gamma.

For the finitely many demands, retain finitely many candidate path
words so that the sum of the probabilities of failure, integrated
over their domains, is below eta/3. Such finite lists exist by
monotone convergence of finite-path connectivity events.

Only finitely many translates of the starting vertex are tested
for marks by these lists. Choose a finite measurable partition P
of X that separates these distinct translates outside a set whose
measure times the number of demands is below eta/3. To obtain P,
use refining finite partitions separating points, freeness, and a
union bound over the finitely many distinct group elements.

Color the atoms of P independently with probability epsilon and
let U be their union. Outside the exceptional set, the finite mark
tests have exactly the independent-vertex law used above. All
S-step validity and H-domain tests are still evaluated on the
original point x; they have not been randomized or approximated.

Retain g_j on D_j intersection U for every j. Add each prefix
demand directly wherever its finite path tests fail, and append
the entire unprocessed H-tail. These maps, joined with S, generate
R for every coloring. By Tonelli, the expected cost of the retained
H-maps is epsilon h; the expected failure repair plus tail is
below eta. Some deterministic coloring therefore has total cost
at most epsilon h+eta. Let epsilon and eta tend to zero to prove
(1). No infinite limiting graphing is asserted to generate.

If F is a finite-cost graphing of S, the consequence is

    C(R) <= c(F),                                         (2)

since for each positive tolerance one can append the corresponding
repair to F. A retained graphing can therefore have many components
without having a positive optimized repair cost.

## 2. Actual use in the conditional-traffic construction

For a finite routing plan, the existing traffic construction retains
the base g_j-edge wherever m_j=E[N_j|X]>=1. Call this graphing F.
Its usual completion pays for every unconnected demand separately.

If the infinite-contact graph of R_F-classes, measured in any fixed
finite-cost generating base graphing H, is connected almost surely,
Section 1 instead yields

    C(X) <= c(F)=sum_j mu{m_j>=1},                         (3)

with graphing copies counted as in the traffic construction. The
same conclusion holds for any other finite-cost base selection F
meeting the hypothesis; F need not be connected initially.

This is an available repair operation. The missing step is still to
construct suitable selections at the desired source budget. Neither
conditional mean traffic nor the existence of a source graphing is
claimed to imply the infinite-contact hypothesis.

## 3. What determinantal deletion does guarantee about cuts

Let H now be a connected countable graph and P_Z the projection onto
the closed span of its finite cycle chains in the edge Hilbert space.
Let 0<=K<=P_Z, and let D be the determinantal deleted-edge process:
for every finite edge set F,

    P(F subset D)=det(K restricted to F).

This is the defining finite-set probability of the process; see
[Lyons, Determinantal probability measures](https://arxiv.org/abs/math/0204325).

No nonempty finite cut of H is entirely deleted almost surely.
Indeed, for a finite cut C=boundary A, its signed cut vector v_C
is nonzero, finitely supported, and perpendicular to every finite
cycle chain. Thus P_Z v_C=0 and K v_C=0. The compression of K to
C is singular, so P(C subset D)=0. There are only countably many
finite edge sets, allowing these zero-probability events to be
excluded simultaneously.

Contract each component of H\D to a vertex, keeping crossing edges
as a multigraph Q. Every nonempty cut of Q is infinite: a finite
one would pull back to an entirely deleted finite cut of H.

However, this conclusion is weaker than the hypothesis of Section 1.
An infinite cut can distribute its edges among infinitely many
different pairs of components, with no individual infinite contact.
Nor does the conclusion alone imply that an independent positive
density sprinkling connects Q, as the next example shows.

## 4. An explicit counterexample to the infinite-cut shortcut

Construct a countable simple graph with distinguished adjacent
vertices u,v recursively. Start with their edge. For every newly
created edge e, attach, for each n>=1, a fresh path of length

    L_n=n+3

between its endpoints. Keep e. All new internal vertices are private
to their path, and perform the same operation on every new edge.
Take the union over finite generations.

Every nonempty cut is infinite. Pick one edge e crossing it. The
infinitely many paths attached directly to e are edge-disjoint,
and each must also cross the cut. Thus no finite deletion of edges
disconnects the graph.

Nevertheless, retain each edge independently with probability p=1/4.
Let r_d be the probability that the two terminals of a depth-d edge
gadget are connected, with r_0=p. Distinct subgadgets have disjoint
edge sets and meet only at the specified series or parallel terminals.
Consequently

    r_(d+1)=p+(1-p)[1-product_(n>=1)(1-r_d^(n+3))].         (4)

For 0<=r_d<=1/2, the union bound gives

    r_(d+1) <= 1/4+sum_(n>=1)(1/2)^(n+3)
             =1/4+1/8=3/8 < 1/2.                        (5)

Induction gives r_d<=1/2 for every d. Every finite open u-v path
in the union is contained in some finite-depth gadget, although
that gadget itself has infinitely many parallel branches. Thus
P(u connected to v)=lim_d r_d<=1/2. The sprinkled graph fails to
be connected with probability at least 1/2.

This graph is not locally finite, as necessarily happens in a graph
with no nonempty finite cut. It is a counterexample to the asserted
property of an abstract component quotient, which can have infinite
degree even when its original graph is locally finite. It is not
a Cayley-graph counterexample, a determinantal example, or a
counterexample to Fixed Price. The extra structure of a genuine
relative determinantal law has not been ruled out as useful.

## 5. Result of the proof attempt

The construction replaces per-request repair by one shared repair
of whole components. The infinite-contact condition is sufficient
and can be used directly in the current traffic framework. The
cycle-operator condition supplies the weaker no-finite-cut property,
but Section 4 rules out using just that property to finish the proof.

For comparison, the positive sprinkling theorem for the free minimal
spanning forest uses a specific conditional law of its outside edge
labels: [Lyons--Peres--Schramm, Lemma 3.23 and Theorem 3.22](https://arxiv.org/pdf/math/0412263).
It is not a theorem about arbitrary component quotients with
infinite cuts. We have not proved an analogue for relative
determinantal deletion, nor realized that law in every prescribed
base action. Those gaps remain explicit.

## 6. The contact hypothesis fails even when relative repair costs zero

Take Gamma=F_2 x Z and its product Cayley graph G=T_4 x Z.
Let F have the uniform spanning forest law. Here FUSF=WUSF:
the group has fixed price one (the infinite-order generators
a,b,z are joined by the commuting pairs a,z and b,z), hence
beta_1(Gamma)=0; the standard spanning-forest identity gives
E deg_FUSF(o)=2+2 beta_1, while WUSF has expected degree two
and is stochastically dominated by FUSF. Thus their laws coincide.
For the fixed-price input see
[Gaboriau's commuting-family theorem](https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf);
the forest identities are also recalled in
[Hutchcroft--Pete, Introduction](https://arxiv.org/pdf/1810.11015).

The graph is nonamenable. By
[Benjamini--Lyons--Peres--Schramm, Theorem 13.7](https://rdlyons.pages.iu.edu/pdf/usf.pdf),
F union an independent Bernoulli(epsilon) bond percolation has
infinitely many components almost surely for all sufficiently
small positive epsilon. Consequently the infinite-contact graph
of F-components cannot be connected almost surely. Indeed, if
it were connected on a set of forest configurations of positive
probability, independent edge sprinkling would connect every
infinite contact on that set, contradicting the cited theorem.

This is compatible with zero optimized relative repair cost on
the same probability space. Let X be the product of the forest
configuration space with an independent nontrivial Bernoulli
Gamma-action, and let S be the subrelation given by the forest
edges. The action on X is free, so C(R_X)=1 by the known fixed
price of Gamma. The forest has infinite components and cost one,
giving C(S)=1 by the aperiodic lower bound. The relative-cost
formula already recorded in Cairn therefore gives

    relC(R_X;S)=C(R_X)-1=0.                               (6)

Thus the infinite-contact hypothesis is not necessary for cheap
repair, even for an actual uniform spanning forest of a Cayley
graph of a known fixed-price group. This conclusion uses the
known value C(R_X)=1; it cannot establish that value for an
unresolved group. Repairs in (6) may use arbitrary group-labelled
partial transformations and depend on the configuration. The
sprinkling theorem concerns independent original Cayley edges.

## 7. An explicit dependent repair that preserves the forest

There is also an elementary positive construction on an explicitly
enlarged probability space. It illustrates what independence of
individual added edges was preventing, without assuming a method
to realize its extra information in an arbitrary action.

Independently of F, mark the vertices of T_4 with probability
delta in (0,1), obtaining A, and mark the integers with probability
eta in (0,1), obtaining B. Add the following subgraph J of G:

* every vertical edge in a column h x Z with h in A;
* every horizontal edge in a layer T_4 x {n} with n in B.

The nonisolated part of J is connected almost surely: A and B
are both nonempty, each chosen vertical column meets each chosen
horizontal layer, and each such column or layer is connected.

Every infinite set T of vertices of T_4 x Z has an infinite
projection onto at least one coordinate. Conditional on F, for
each of its trees T, infinitely many distinct first coordinates
give an A-mark in that projection almost surely, or infinitely
many distinct second coordinates give a B-mark. In either case
T intersects J. There are countably many trees, so they all
intersect its connected nonisolated part simultaneously. Hence

    F union J is connected almost surely.                (7)

The law is Gamma-invariant. Counting one positive vertical and
two positive horizontal generators, the added cost is at most

    delta+2 eta,

which tends to zero. Every original F-edge is retained. The
argument works for any independent random spanning forest with
only infinite components; it does not require indistinguishability.
These are shared whole-column and whole-layer connections, not
independent bond sprinkling. This is a reconstruction using the
known product geometry, not a new fixed-price family.

### The realization issue remains explicit

The marking law used in (7) cannot be copied as a factor of a
Bernoulli Gamma-action. Membership of a column in A is a nontrivial
event invariant under the infinite Z-subgroup. Restriction of a
Bernoulli Gamma-action to that subgroup is again a Bernoulli action
after regrouping coordinates into its cosets, and is ergodic.
It has no invariant event of measure delta in (0,1). Moreover A
is recoverable from the vertical-edge indicators of J, so this
obstruction applies to reproducing the helper graph law itself.

Equation (7) supplies a concrete connected repair on the product
with the two marking spaces. It does not make J measurable on
the original base action. Equation (6) separately guarantees
arbitrarily cheap repairs there because this group's fixed price
is already known; it does not identify those repairs with J.
For the universal problem, reproducing the attainable cost while
discarding the marking law is still the unproved step.
