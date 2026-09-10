# Critical quotient percolation: root bias, heavy degrees, and expansion

Date: 2026-09-09. These are written deductions, not Lean proofs or claims
of novelty. Benjamini--Schramm remains open in this investigation. The aim
is to retain the actual independent sprinkling law while locating the
failure of an exploration argument based on expansion and mean degree.

## 1. The actual critical quotient

Fix G=Cay(Gamma,S), of finite degree d, and c=p_c(G). Let h>0 satisfy
|boundary_E W|>=h|W| for every nonempty finite vertex set W. Use independent
uniform edge labels U_e. Write omega_c for the entire configuration of
indicators 1{U_e<=c}. Its clusters are finite almost surely, by the
Benjamini--Lyons--Peres--Schramm critical-finiteness theorem [CF].

For each such configuration define the multigraph Q:

* Its vertices are the c-clusters C, with mass m(C)=|C|.
* Each original edge between different clusters becomes a separate edge
  of Q. Parallel edges are retained. Edges internal to a cluster are omitted.

Q is connected, infinite, and locally finite. Put B(C)=deg_Q(C), counting
parallel edges. For any finite set A of its vertices, lift A to the finite
original set W=union_{C in A} C. The edge boundaries agree, so

    |boundary_Q A| >= h sum_{C in A} m(C),
    h m(C) <= B(C) <= d m(C).                            (1)

In particular |boundary_Q A| >= (h/d) sum_{C in A} B(C).
Thus the normalized edge expansion is uniformly positive even though
the degrees are unbounded.

Conditional on omega_c, the residual labels

    V_e=(U_e-c)/(1-c),             for edges closed at c,

are independent uniforms on (0,1). This follows first for every finite
collection from product conditioning, and then for the countable product
by its finite-dimensional distributions. For t in [0,1], set

    q=c+(1-c)t.

The q-clusters in G correspond exactly to the t-Bernoulli bond clusters
in Q, under the map sending an original vertex to its c-cluster. Indeed,
each c-cluster is already connected, and every new intercluster edge is
retained precisely when V_e<=t. Conversely every open quotient path lifts
to an open original path. Since every c-cluster is finite, a quotient
component is infinite if and only if its lifted original component is
infinite. Thus this correspondence preserves the number of infinite
components, configuration by configuration in the coupling.

In particular p_c(Q)=0 for almost every omega_c. For each rational t>0,
q>c, so the original process has an infinite component almost surely.
Disintegration and a countable intersection give the corresponding
quenched assertion for all rational t. Existence is increasing in t,
which supplies the assertion for every t>0 and the threshold conclusion.

For each FIXED t, disintegration also transfers the original almost-sure
cluster count at q to the quenched quotient law for almost every omega_c.
This holds simultaneously over any specified countable set of t values.
We do not interchange the uncountable parameter quantifier with the
exceptional configuration set, or assume a general uniqueness-monotonicity
theorem for arbitrary nontransitive quotient graphs.

This quotient is not a new model with adjustable independent probabilities
on the original generators. It is the prescribed Bernoulli process after
revealing its critical configuration. In particular, replacing a bundle
of k parallel edges by one edge of retention t would change its law: the
connection probability of that bundle is 1-(1-t)^k.

## 2. The quotient root must be reweighted

Rooting Q at C_c(o) under the original law samples clusters in proportion
to their vertex mass. Put

    kappa = E[1/m(C_c(o))] > 0,
    E_dagger F = (1/kappa) E[F(Q,C_c(o))/m(C_c(o))].         (2)

This is a probability law on rooted mass-marked multigraphs. It is
equivalent to selecting one vertex by independent continuous priorities
in each finite cluster and conditioning o to be the selected vertex,
then forgetting that priority decoration. We use (2) directly.

The law P_dagger is unimodular. Here is the full mass-transport argument.
For a nonnegative invariant transport f(Q,C,D), lift it to original
vertices by

    F(omega,u,v) = f(Q,C_c(u),C_c(v))/(m(C_c(u))m(C_c(v))).

Summing over v gives (1/m(C_c(u))) sum_D f(Q,C_c(u),D).
Summing over u gives the corresponding incoming expression. The original
Cayley mass-transport principle equates their expectations. Dividing by
kappa gives exactly the outgoing-equals-incoming identity for (2).
All exchanges of sums use nonnegativity, so no moment assumption is hidden.

For every nonnegative rooted quotient observable F,

    E_dagger[m F] = E[F]/kappa.                            (3)

Consequently

    E_dagger m = 1/kappa,
    h/kappa <= E_dagger B <= d/kappa.                     (4)

Thus the unimodular quotient has finite mean mass and finite mean degree.
The change of measure depends only on omega_c. It does not change the
conditional independent law of the residual labels in Section 1.

## 3. The second moments nevertheless diverge

The original critical susceptibility is infinite:

    E |C_c(o)| = infinity.                               (5)

This is an imported classical theorem, stated explicitly as Proposition
1.2 of Duminil-Copin--Tassion [DT], not inferred from critical finiteness.
That paper proves it using its finite-set sharpness criterion. In our
bounded-degree setting all its summability hypotheses hold.

Equations (1), (3), and (5) imply

    E_dagger m^2 = (E m)/kappa = infinity,
    E_dagger B^2 >= h^2 E_dagger m^2 = infinity.            (6)

If the unimodular quotient root law is further biased by degree, define

    E_edge F = E_dagger[B F]/E_dagger B.

Then

    E_edge B = infinity.                                 (7)

This is the degree-biased root law, not an assertion that a particular
exploration samples independent vertices from it. Such independence has
not been proved. The conclusion is narrower and rigorous: replacing a
size-biased exploration cost by the finite unweighted mean in (4) loses
an infinite factor. A branching estimate using E_edge(B-1) has infinite
mean at every positive sprinkling parameter and supplies no subcritical
bound. It does not prove uniqueness, nonuniqueness, or independent
branching of the exploration.

This calculation identifies an actual obstruction in the prescribed model,
rather than an arbitrary partition counterexample. Finite mean quotient
degree, nonamenability, and p_c(Q)=0 are all compatible because the second
degree moment diverges.

## 4. Expansion by itself allows uniqueness at every positive parameter

The following deterministic example tests the expansion-only inference.
It does NOT have the unimodular quotient law in Section 2.

Let L_k, k>=0, be disjoint layers with |L_k|=n_k=2^k. Join each vertex of
L_k to every vertex of L_{k+1}, with no other edges. This gives a connected
locally finite graph H with unbounded degrees. Give each vertex weight
m(v)=deg_H(v). Its unique vertex in L_0 has degree 2; vertices in L_k for
k>=1 have degree 5*2^{k-1}.

Orient edges from L_k to L_{k+1}. For k>=1, outdegree=4*indegree, hence
outdegree-indegree=(3/5)deg. The bottom vertex has divergence equal to its
degree. Summing divergence on a finite vertex set A cancels internal
edges. Net outward flow is bounded by the number of boundary edges, so

    |boundary_H A| >= (3/5) sum_{v in A} deg_H(v).          (8)

This is a uniform normalized expansion bound, and deg_H(v)/m(v)=1.
Nevertheless, Bernoulli bond percolation on H has a unique infinite
component almost surely at EVERY fixed p>0. In fact that component is
cofinite.

To prove this, consider the random bipartite graph between L_k and L_{k+1},
of sizes n and 2n. If it is disconnected, some component vertex set A
has size j with 1<=j<=3n/2. Write a=|A intersect L_k| and b=|A intersect
L_{k+1}|. Its edge boundary in the complete bipartite graph has size

    a(2n-b)+b(n-a) = n(2a+b)-2ab
                  >= nj-j^2/2 >= nj/4.                  (9)

For a particular A, the probability all these edges are closed is at
most exp(-pnj/4). A union bound over vertex subsets therefore gives

    P(the bipartite graph is disconnected)
      <= sum_{j=1}^{floor(3n/2)} (3n exp(-pn/4))^j
      <= 6n exp(-pn/4)                                  (10)

once 3n exp(-pn/4)<=1/2. With n=2^k these probabilities are summable.
Borel--Cantelli shows that all sufficiently high consecutive-layer
bipartite graphs are connected. Their union is a connected open graph
containing every vertex above some finite level. The omitted lower
levels are finite, proving the claim. Intersecting over rational p>0 in
the monotone coupling and then using cofiniteness gives the simultaneous
version if desired. Thus p_c(H)=p_u(H)=0 under either the infimum or
upper-phase definitions of uniqueness threshold.

The example cannot carry ANY unimodular probability law supported on
rootings of this fixed graph. Its unique degree-two vertex is intrinsic.
Let every vertex send one unit of mass to that vertex. Expected outgoing
mass is one. Expected incoming mass is zero if the root is never that
vertex, and infinite if it has positive probability of being that vertex.
Either possibility contradicts mass transport. Thus (8) refutes only an
expansion-only argument; it does not refute the stronger statement about
the actual critical quotient, or the Cayley-graph conjecture.

## 5. The remaining task and verification

This investigation has not proved that the quotient has a nonuniqueness
parameter t>0. Establishing it on a nonempty interval for every critical
quotient would transfer back to the requested statement through Section 1.
The Palm law, independent edge sprinkling, and its origin in critical
Bernoulli percolation must be retained in such an argument. The layered
example cannot replace those hypotheses. Conversely, the infinite second
moment blocks the elementary exploration bound even with the correct law.

`scripts/replay_critical_quotient.py` verifies finite contraction identities,
parallel-edge retention, the Palm normalization and an explicit failure of
unweighted mass transport, and the layered cut inequalities. Its exact
finite calculations are not proofs of critical finiteness, infinite
susceptibility, the infinite mass-transport principle, or the universal goal.
All execution and Cairn validation take place on MSI. The compiled graph
records these deductions without marking Benjamini--Schramm established.

## Sources

[CF] Benjamini--Lyons--Peres--Schramm, *Critical percolation on any
nonamenable group has no infinite clusters* (1999); a recent exposition
is Chu, Theorem 1.1: https://arxiv.org/abs/2608.06644.

[DT] Duminil-Copin--Tassion, *A new proof of the sharpness of the phase
transition for Bernoulli percolation and the Ising model*, arXiv:1502.03050v3,
Proposition 1.2, printed page 4: https://arxiv.org/pdf/1502.03050.

For the general unimodular framework see Aldous--Lyons, *Processes on
Unimodular Random Networks*: https://arxiv.org/abs/math/0603062. Section 2
above proves the particular reweighting identity rather than importing
an unspecified contraction theorem.
