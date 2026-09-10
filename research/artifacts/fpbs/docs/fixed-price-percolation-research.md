# Cost, percolation thresholds, and the routing obstruction

Date: 2026-09-08

## Status and scope

Neither the universal Fixed Price problem nor the universal Benjamini–Schramm
nonuniqueness conjecture is proved or refuted in this note. The results below
are a quantitative cost–percolation estimate, an explicit routing obstruction,
and a compactness obstruction. They are mathematical arguments, not Lean
formalizations. No claim of priority is made for these consequences of the
standard cost/percolation machinery. In particular, the qualitative implication
in Section 5 is already due to Lyons [L].

Fixed Price is understood for countably infinite groups and essentially free
probability-measure-preserving actions on standard probability spaces. The
percolation statements here concern simple, locally finite, undirected Cayley
graphs and independent **bond** percolation. They do not assert a theorem for
arbitrary nontransitive networks or arbitrary dependent percolations.

## 1. The relevant Cairn material

In the supplied `group-approximation-main (31).zip` snapshot, the closest relevant
note found was `notes/TRUE_ROUTED_HOLONOMY_PHASE_REPAIR.md`, dated 2026-08-11.
Its Section 1 expressly withdraws a cost-one-only compact-skew permanence
argument: small graphing excess does not control the lengths of routes
expressing external transformations. Its positive statement retains both
routed-holonomy control and phase compatibility. Sections 6–7 below address
this metric obstruction, not the validity of the conditional phase theorem.

The node `research/non-ce-relation-is-not-treeable.md` concerns non-treeability
of certain orbit relations. Non-treeability alone neither exhibits different
costs of two free actions of one group nor proves a Bernoulli nonuniqueness
interval. Its free-group stabilizer-realizing action is not an essentially
free free-group action. Thus it cannot be substituted directly for a free
action in Fixed Price. This note does not independently certify all the
operator-algebraic prerequisites of that node.

No dedicated proof of either target was located in the inspected snapshot.
The archive audit and exact source copies accompany this note. The supplied
whole-project Cairn check has unrelated baseline errors; only the isolated
addition is validated here.

## 2. Definitions and imported facts

Let Gamma be an infinite finitely generated group, S a finite symmetric
generating set not containing the identity, and G = Cay(Gamma,S), of degree
d = |S|. Write o for the identity vertex.

For a free p.m.p. action a, its cost is the infimum of the costs of graphings
which generate its orbit relation. For a simple undirected graphing the cost
is half its mean degree [G]. It is essential to distinguish the cost of a
particular graphing from this infimum.

Set

    C*(Gamma) = sup { Cost(a) : a is a free p.m.p. action of Gamma }.

The Abért–Weiss theorem implies that C*(Gamma) equals the cost of a nontrivial
Bernoulli action [AW]. Also every free action of an infinite group has cost at
least 1 [G]. Thus C* = 1 is equivalent to fixed price one, whereas C* > 1 does
not decide whether different actions have different costs.

Couple bond percolations by i.i.d. edge uniforms U_e, declaring e open at p
when U_e <= p. Let K_p(o) be the root cluster. Define

    kappa(p) = E[1 / |K_p(o)|],     with 1/infinity = 0.

This is a finite-cluster density, not the infinite-cluster probability theta(p).
Let p_c be the infimum of parameters with positive infinite-cluster
probability, and p_u the infimum of parameters with a unique infinite cluster
almost surely. The usual transitive Bernoulli-percolation phase theorem
identifies (p_c,p_u), when nonempty, with the infinitely-many-infinite-clusters
phase; see [L] and its primary references.

## 3. An endpoint-continuity lemma

**Lemma 1.** The function kappa is continuous on [0,1]. More quantitatively, let
B_R(o) be the radius-R ball in G and let K_{p,R}(o) be the open root component
in the induced subgraph on B_R(o). Then

    0 <= E[1/|K_{p,R}(o)|] - kappa(p) <= 1/(R+1)

for every p in [0,1] and integer R >= 0.

**Proof.** The restricted cluster is contained in the full cluster. If the full
cluster is contained in the ball, the two clusters agree: every open path in
that cluster stays in the ball. Otherwise, an open path from o first exiting
the ball has at least R+1 distinct vertices before it exits. Its initial
segment lies in the restricted cluster. Consequently that restricted cluster
has at least R+1 vertices, and the difference of reciprocals lies between
zero and 1/(R+1). This also holds when the full cluster is infinite.

Taking expectations proves the displayed bound. For fixed R the expectation
on the left is a polynomial in p, because only finitely many edges occur in
the ball. The bound is uniform in p, so kappa is a uniform limit of continuous
functions. QED.

In particular, this lemma does not assume absence of infinite clusters at
p_c, uniqueness at p_u, or continuity of theta.

## 4. Quantitative cost–threshold bound

**Theorem 2.** For the preceding Gamma and G,

    C*(Gamma) - 1
      <= (d/2)(p_u - p_c) - [kappa(p_c) - kappa(p_u)].                 (1)

In particular,

    p_u - p_c >= (2/d)(C*(Gamma) - 1).                               (2)

The correction in (1) is nonnegative because kappa is nonincreasing.

### 4.1 Realizing the construction in a genuinely free Bernoulli action

Use a Bernoulli action whose vertex marks contain enough independent uniform
coordinates. For each half-edge (g,s), take a distinct uniform coordinate
V_{g,s}. For the undirected edge e = {g,gs}, put

    U_e = (V_{g,s} + V_{gs,s^{-1}}) mod 1.

This definition is unchanged upon reversing the edge. Different edges use
disjoint coordinates, so the resulting edge labels are independent uniforms.
The construction is equivariant under left translations, including when S
contains elements of order two. Further independent continuous vertex marks
provide measurable tie-breaking. The full action on the vertex-label space
is still a free Bernoulli action, to which [AW] applies.

### 4.2 Finite q-clusters and band edges

Fix q < p_c, and fix p > q at which there is a unique infinite p-cluster I
almost surely. Such a p exists at least at p=1. All q-clusters are finite.
Choose an equivariant measurable spanning tree in each q-cluster, for example
by rooting at its smallest vertex mark and using breadth-first search with
label tie-breaking. Let F_q be their union.

A finite cluster with n vertices contributes n-1 edges. The mass-transport
principle therefore gives

    (1/2) E deg_{F_q}(o) = 1 - kappa(q).                              (3)

Add every edge with q < U_e <= p. These edges have intensity d(p-q)/2 and are
disjoint from F_q. The resulting graph J has exactly the p-clusters as its
components: the q-trees preserve every q-connection, and all the remaining
p-open edges are restored. No minimum-spanning-forest connectivity assertion
on infinite clusters is being used.

### 4.3 Reconnecting the finite p-clusters

For each finite p-cluster C, define its height

    h(C) = min { d_G(v,I) : v in C }.

This is a finite positive integer. Among vertices v attaining this minimum,
choose one by its continuous mark; then choose a neighbor w with

    d_G(w,I) = h(C) - 1,

breaking the finitely many ties equivariantly. The edge {v,w} is p-closed:
if w belonged to C, the minimum defining h(C) would be smaller. Select this
one edge for C.

The p-cluster containing w is either I or a finite cluster of strictly smaller
height. Thus repeated chosen bridges reach I in finitely many steps. The
resulting graph H is connected and spans all of G. An edge cannot be chosen
from both endpoint clusters, because heights cannot decrease in both
directions. All these bridges are disjoint from J.

There is exactly one selected bridge for each finite p-cluster. To compute
its intensity, have every vertex in a finite C send mass 1/|C| to the source
vertex of C's selected bridge. The sent mass has expectation kappa(p), while
the received mass is one precisely at a bridge source. Translation invariance
and mass transport give bridge-source intensity kappa(p). Each selected edge
has exactly one source; its unoriented edge intensity is therefore also
kappa(p), equivalently half its expected incident degree.

All choices are measurable: cluster membership, finiteness, distance to the
measurable unique infinite cluster, finite minima, and label tie-breaks are
measurable operations. Orientation by independent vertex marks converts H
into a graphing counted once per undirected edge, if a partial-isomorphism
presentation is preferred.

Combining the three disjoint edge sets gives a graphing of the entire free
Bernoulli orbit relation with cost exactly

    1 - kappa(q) + (d/2)(p-q) + kappa(p).

Since action cost is an infimum,

    C*(Gamma) <= 1 - kappa(q) + (d/2)(p-q) + kappa(p).                (4)

### 4.4 Taking limits without assuming endpoint behavior

If p_c < 1, let q increase to p_c. By the definition of p_u as an infimum,
there are uniqueness parameters p tending to p_u; when p_u=1 one may simply
use p=1 throughout. Lemma 1 allows passage to the limit in (4), proving (1).

If p_c=1, then p_u=1. Take q increasing to 1 and p=1 directly in (4); Lemma 1
again gives C* <= 1 and the same conclusion. Thus the theorem also covers
this endpoint case. Monotonicity of kappa gives (2). QED.

## 5. Consequences and a sharpness check

**Corollary 3 (Lyons's qualitative implication, recovered).** If even one
Cayley graph of Gamma has p_c=p_u, then Gamma has fixed price one. Equivalently,
if Gamma does not have fixed price one, every Cayley graph of Gamma has a
nonuniqueness interval.

Indeed, (1) yields C* <= 1 under threshold equality, and the general lower
bound makes the cost of every free action exactly 1. Lyons [L] already proved
this qualitative conclusion using [AW]. The quantitative ledger above should
not be advertised as a first solution to that known part of the problem.

For the standard Cayley tree of the free group F_r, r>=2, d=2r. Its branching
process has offspring distribution Binomial(2r-1,p), so p_c=1/(2r-1).
For p_c<p<1, deleting a specified edge has positive probability of leaving
infinite clusters on both sides. Thus uniqueness is impossible; the standard
0/1/infinity theorem for the number of infinite clusters implies p_u=1.
All free actions have cost r because their free-generator graphings are
treeings [G]. For q<p_c, every q-cluster already is a tree, giving

    kappa(q) = 1-rq.

Lemma 1 then gives kappa(p_c)=(r-1)/(2r-1), while kappa(1)=0. Formula (1) becomes

    r-1 <= r(1-1/(2r-1)) - (r-1)/(2r-1) = r-1.

Hence equality holds for every r>=2. This establishes sharpness on regular
Cayley trees, not uniqueness or novelty of the inequality.

## 6. Explicit reciprocal routing obstruction

Let Gamma = F_r x Z, r>=2, with standard Cayley graph T_{2r} square Z. For
0<epsilon<1 form an invariant random spanning subgraph H_epsilon by retaining
all vertical Z edges and retaining each horizontal tree edge at each integer
height independently with probability epsilon. Use one family of uniform
labels to realize every epsilon on the same free Bernoulli action.

**Proposition 4.** Each H_epsilon is connected almost surely and its graphing
cost is 1+r epsilon. For adjacent horizontal vertices x=(e,0), y=(a,0), their
shortest H_epsilon-path distance D_epsilon satisfies

    E D_epsilon = (2-epsilon^2)/(epsilon(2-epsilon)).                 (5)

Writing delta_epsilon = r epsilon for graphing cost minus one gives

    delta_epsilon E D_epsilon
      = r + r epsilon(1-epsilon)/(2-epsilon) > r,                    (6)

with limit r as epsilon tends to zero. In particular, cost excess tending to
zero does not, by itself, imply that cost excess times mean replacement
length tends to zero.

**Proof.** Every vertical fiber is connected. For every adjacent pair of
fibers there are infinitely many independent opportunities for a horizontal
bridge; almost surely at least one occurs. There are only countably many
adjacent pairs, so almost surely all such pairs are joined and H_epsilon is
connected. Its mean degree is 2+2r epsilon, giving the stated graphing cost.

Let M_epsilon be the smallest absolute height at which a retained horizontal
edge crosses the specified base-tree edge {e,a}. Any path from x to y must
cross that particular base-tree edge, because removing it disconnects the
base tree. A crossing at height k requires at least 2|k| total vertical steps
and at least one horizontal step. Going vertically to a nearest retained
bridge, crossing it, and returning vertically achieves this bound. Thus

    D_epsilon = 2M_epsilon + 1.

For every integer m>=0, independence gives

    P(M_epsilon > m) = (1-epsilon)^(2m+1).

The nonnegative-integer tail-sum formula and a geometric series imply

    E M_epsilon = (1-epsilon)/(epsilon(2-epsilon)),

which proves (5) and (6). For every fixed R, P(D_epsilon>R) tends to 1.
These are lower bounds on shortest routes, not merely inefficient chosen
routes. QED.

Taking epsilon to zero also proves cost of this Bernoulli action equals one,
and [AW] gives the familiar fact that F_r x Z has fixed price one. This class
was already known [G]; the example is not a new class of fixed-price groups.
Most importantly, the varying values 1+r epsilon are costs of graphings of
one action, not different costs of different actions. The action's cost is
the infimum, namely one. Accordingly this is not a counterexample to Fixed
Price. Nor does it refute the conditional routed-holonomy and phase-compatible
criterion in the supplied Cairn note.

## 7. A general qualitative obstruction by compactness

The example in Section 6 has a qualitative extension using a standard cost
fact: an infinite group with a free p.m.p. action whose cost-one infimum is
attained by a graphing must be amenable [G, paragraph following the
Ornstein–Weiss discussion].

**Proposition 5.** Let G be a Cayley graph of a nonamenable finitely generated
group. Suppose H_n are invariant random connected spanning subgraphs of G
with (1/2)E deg_{H_n}(o) tending to one. It is impossible that, for every
s in S, the family d_{H_n}(o,s) is uniformly tight in n. In particular, it is
impossible that all these expectations are uniformly bounded.

**Proof.** Otherwise, compactness of {0,1}^{E(G)} gives a weakly convergent
subsequence of the laws, with invariant limit law for a subgraph H. Expected
root degree passes to the limit because it depends on finitely many edge
coordinates, so (1/2)E deg_H(o)=1.

For fixed R, the event d_H(o,s)<=R is a cylinder event: a path of length at
most R stays within the ambient ball B_R(o). Its probability therefore also
passes to the limit. Uniform tightness, followed by R tending to infinity,
gives P(o connected to s in H)=1. Translation invariance, countability, and
connectedness of G imply that H is connected almost surely.

Take the invariant law of H, and multiply its group action by an independent
free Bernoulli action. The diagonal action is free. The connected equivariant
spanning graph H supplies a graphing of this entire free action, with graphing
cost exactly one. The general cost lower bound makes this an attained
cost-one infimum. The quoted attainment theorem forces amenability, a
contradiction. Uniformly bounded means would imply uniform tightness by
Markov's inequality. QED.

This argument does not give the reciprocal rate in Proposition 4. It shows
why a general cost-only uniform route bound is unavailable even before phase
errors are considered. A percolation-specific additional argument would be
needed to obtain a contradiction from a hypothetically collapsed threshold
window.

## 8. Exact remaining mathematical targets

For Benjamini–Schramm, Corollary 3 reduces the remaining class precisely to
nonamenable groups of fixed price one. What is still required is

    p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S))

for every such Gamma and every finite generating set S. In this class,
setting C*=1 and p_c=p_u in (1) gives 0<=0, not a contradiction. Showing that
some generating set works would not settle the every-generating-set question.

For Fixed Price in the finitely generated setting, [AW] supplies only

    Cost(a) <= C*(Gamma)

for each free a. The reverse inequality for arbitrary a, or an explicit
strict example, is still missing. The proofs above supply neither. They also
do not resolve the additional generality of countable groups which are not
finitely generated.

Known developments do not close these gaps: [K] proves fixed price one for
products of two infinite countable groups; [S] gives a product-neighbourhood
criterion and extensions to locally compact groups; [CS] proves the
nonuniqueness conjecture for Cayley graphs of acylindrically hyperbolic groups.
These are important classes, not replacements for the universal quantifiers.

## 9. Verification and research-graph semantics

`scripts/replay.py` exhaustively checks the finite spanning-forest/reconnection
ledger in 3,753 nested configurations on five small graphs, the deterministic
finite-ball bound in 5,168 cases, the geometric-series routing identities at
40 rational parameter pairs, and the regular-tree sharpness identity at 49
ranks. The saved output is `research/artifacts/replay.json`.

These checks only verify the stated finite combinatorics and rational
identities. They do not verify infinite measurability, mass transport, imported
cost theorems, or either universal conjecture. The written arguments above
address those infinite steps using the indicated published results.

Cairn compilation checks identifiers, artifacts, dependencies and implication
structure. A compiled ESTABLISHED node records an asserted written proof or
an explicitly cited published theorem; it is not automated theorem proving.
The two universal goal nodes and the fixed-price-one percolation kernel are
left OPEN. The original archive is not modified by this addition.

## References

[AW] Miklos Abert and Benjamin Weiss, *Bernoulli actions are weakly contained
in any free action*, arXiv:1103.1063v2 (2011), especially Corollary 2.
https://arxiv.org/html/1103.1063v2

[L] Russell Lyons, *Fixed Price of Groups and Percolation*, arXiv:1109.5418v1
(2011), published in Ergodic Theory and Dynamical Systems 33 (2013), 183–185.
https://arxiv.org/html/1109.5418v1

[G] Damien Gaboriau, *What is ... cost?*, Notices of the AMS 57 (2010),
1295–1296; arXiv:1011.2294v1. Used for graphing/action cost, the lower bound,
treeings, free-group costs, and the attained-cost-one/amenability fact.
https://arxiv.org/html/1011.2294v1

[K] Ali Khezeli, *Products of Infinite Countable Groups Have Fixed Price One*,
arXiv:2509.08325v2 (2025).
https://arxiv.org/html/2509.08325v2

[S] Raz Slutsky, *A Product-Neighbourhood Criterion for Fixed Price One*,
arXiv:2607.20273v1 (22 July 2026).
https://arxiv.org/html/2607.20273v1

[CS] Inhyeok Choi and HoJoon Seo, *Percolation in acylindrically hyperbolic
groups*, arXiv:2508.08932 (2025).
https://arxiv.org/abs/2508.08932
