# Closed walls and the probability cost of search

This develops the balanced target-directed exploration in
`exploration-information.md` and `search-geometry.md`. It proves an
exponential deterministic obstruction and a summable family of Bernoulli
lower certificates. Neither is the conditional expected-query upper bound
needed to prove Benjamini--Schramm. The universal goal remains OPEN.

## 1. Search and a radial observation

Work on the degree-six Cayley graph G=T_4 x Z. Fix an edge xy of T_4,
and take the two search roots to be (x,0) and (y,0). Deleting xy divides
T_4 into rooted ternary half-trees A and B. The corresponding half-products
are A x Z and B x Z. For v in A x Z, put r(v)=d_G((x,0),v). Then
d_G(v,(y,0))=r(v)+1; the analogous identity holds in the other half.

Each side queues oriented candidates (u,v) with priority

    depth(u)+1+beta*d_G(v,opposite_root),   beta >= 0,

using depth at first discovery and insertion-order ties. The two sides
alternate fresh queries, share all answers, and finish when they meet
or either side exhausts its frontier. All statements here concern the
uncapped search; an infinite run has query count N=infinity. The executable
replay uses the same engine with an explicit censoring cap.

Before the first open crossing between the halves, every vertex v with
an open ambient geodesic from its own root has first-discovery depth
r(v). To see this, suppose v were the first such vertex discovered with
depth d>r(v). On a fixed open radial geodesic to v, the first undiscovered
vertex w has a discovered predecessor of correct depth. Its queued
candidate has priority

    r(w)+beta*(r(w)+1)
       <= r(v)+beta*(r(v)+1)
       < d+beta*(r(v)+1).

It would have been processed before the purported discovery of v, a
contradiction. This is a first-counterexample argument on discovery
times; all geodesic prefixes are themselves open radial geodesics.
Consequently, if that side is about to discover a vertex of radius at
least m+1, every vertex with an open radial geodesic and radius at most
m has already been discovered. Otherwise the first missing prefix has
priority at most m+beta*(m+1), strictly below the imminent discovery's
priority, which is at least (m+1)+beta*(m+2).

## 2. A finite wall forces exponentially many queries

**Proposition 1.** Close exactly the copies of xy at heights |z|<=m,
and open every other edge, for an integer m>=0. For every finite
beta>=0 the search connects, its shortest possible connecting path has
length L=2m+3, and

    N >= 3^(m+1)-m-3.                                      (1)

In particular, even beta>1 has no deterministic polynomial query bound
in shortest open path length on this fixed Cayley graph.

**Proof.** Every connecting path crosses xy at height |z|>=m+1, and
therefore has at least 2m+3 edges. Vertical travel to height m+1, a
single crossing, and vertical travel back realizes this length. The
configuration is connected. Finite sublevel sets of the search priority
make each side exhaustive: only finitely many vertices have discovery
depth below a fixed bound on a locally finite graph, and priority is
at least candidate depth. Alternation of fresh queries cannot starve a
side, and only finitely many cached candidates are available without
new discoveries. Hence the search eventually finds a connection.

Before its first open crossing, the crossing side has discovered its
own endpoint of that crossing, at vertical height of absolute value
at least m+1. At the first discovery on that side of radius at least
m+1, the observation in Section 1 forces prior discovery of its entire
half-product ball of radius m, since the half-product is all open.
There are 3^r half-tree vertices at tree depth r and 2(m-r)+1 allowed
heights. Thus the ball has size

    sum_{r=0}^m 3^r*(2(m-r)+1) = 3^(m+1)-m-2.

Each nonroot discovery uses a distinct queried-open internal edge.
Before the first open crossing the other side stays in its disjoint
half, so those discoveries cannot be obtained from open answers of the
other side. There are at least ball-size minus one fresh queries,
proving (1). The argument is independent of the tie order. QED.

**Corollary 1.1 (expansion and removal of finite branches do not fix
this schedule).** Every wall configuration in Proposition 1 has edge
Cheeger constant at least 2 and normalized edge Cheeger constant at
least 1/3, uniformly in m. Every open edge belongs to an open four-cycle.
There are no bridges or finite pieces attached by a single bridge,
and iterative deletion of vertices of degree at most one removes
nothing. Nevertheless the exponential query lower bound (1) holds.

**Proof.** In each of the two rooted ternary half-trees, orient tree
edges from parent to child. For a finite set U at one fixed height,
there are 3|U| child edges with parent in U, and at most |U|-1
of them have both endpoints in U when U is nonempty: these internal
edges form a finite forest. Thus at least 2|U| child edges leave U.
These edges are all open, because none crosses the distinguished
tree edge xy. Apply this count separately in both halves and at each
height for any finite nonempty vertex set S. The counted outgoing
edges are distinct, so |boundary_open S|>=2|S|. Since every degree
is at most 6, this also gives

    |boundary_open S| / sum_{v in S} deg_open(v) >= 1/3.

An open horizontal edge other than a copy of xy forms a four-cycle
with its translate one level higher. An open copy of xy at |z|>m
forms a four-cycle with the adjacent copy farther from height zero.
A vertical edge forms a four-cycle using any horizontal neighbor in
the same half-tree. All the specified edges are open. Hence no open
edge is a bridge. Each vertex has degree at least 5, which also proves
the assertion about iterative leaf removal. QED.

This is a deterministic obstruction for the specified target priorities,
not for every algorithm. In particular an efficient algorithm might
use the product geometry to find a route around the wall. The corollary
only rules out controlling this schedule's excess queries by a sum of
finite dangling-branch sizes, or deriving a polynomial detour bound
for it from a positive Cheeger constant alone. It makes no Bernoulli
expected-cost assertion.

The all-open remainder in this example has probability zero for an iid
parameter q<1. A completed run nevertheless has a finite transcript.
If its answers include U open and C closed edges, that exact transcript
has Bernoulli probability

    q^U*(1-q)^C.                                           (2)

Indeed, fix the deterministic search and its roots. Inductively, its next
query and its stopping decision are functions of earlier answers. The
event of the specified terminal transcript is exactly the cylinder
specifying those distinct edges. No restrictions on unqueried edges
are needed. In particular the probability at q=1/2 is 2^(-N).
Charging just (1-q)^(2m+1) while importing the all-open search volume
omits the open-answer cost and is invalid.

## 3. A Bernoulli wall certificate and its summable budget

Now take genuine iid Bernoulli(q) edges, with 0<q<1. Let W_m be the
event that all 2m+1 copies of xy at |z|<=m are closed. At height zero,
let V_A,m be the number of vertices reached from x using only open
edges of its rooted ternary half-tree, truncated at tree depth m.
Define V_B,m analogously. The two volumes are independent, identically
distributed, and independent of W_m, because the three sets of edges
are disjoint. Counting the unique radial paths gives

    E V_A,m = sum_{r=0}^m (3q)^r.

**Proposition 2.** For the same uncapped search and each m>=0,

    N >= R_m := 1_{W_m}*(min(V_A,m,V_B,m)-1).                (3)

Moreover,

    E sup_{m>=0} R_m <= E sum_{m>=0} R_m
      <= 3*(1-q)^3 / ((2-q)*(1-3q*(1-q)^2))
      <= 27/5.                                            (4)

**Proof of (3).** Outside W_m the certificate is zero. On W_m, suppose
first that an open crossing is queried. Prior to it, the crossing side
has discovered a vertex at radius at least m+1 in its own half. By
Section 1 it has already discovered all its height-zero tree vertices
with open radial paths of length at most m. This requires at least
V_A,m-1 or V_B,m-1 fresh internal queries, respectively. The side that
escapes can be chosen by the answers, which is why the minimum is used.

If a side exhausts its frontier before any open crossing, its discovered
set is its complete finite open component and contains the corresponding
height-zero tree cluster. The same counting applies. If neither event
ever occurs, the run has infinitely many fresh queries: finite queries
give finitely many discoveries and queued candidates, so cannot support
an infinite run. Then (3) is immediate. These cases exhaust the uncapped
algorithm. QED.

**Proof of (4).** Nonnegativity and Tonelli's theorem give

    E sum_m R_m
      <= sum_{m>=0} (1-q)^(2m+1)*sum_{r=1}^m (3q)^r.

Set a=(1-q)^2 and b=3q. Interchanging the nonnegative sums evaluates
the last expression as

    (1-q)/(1-a) * ab/(1-ab)
      = 3*(1-q)^3 / ((2-q)*(1-3q*(1-q)^2)).

Both geometric series converge: a<1 and

    4/9 - 3q*(1-q)^2 = (1-3q)^2*(4-3q)/9 >= 0.

Thus 1-ab>=5/9. Using 2-q>=1 and (1-q)^3<=1 gives the
stated uniform bound. Finally sup_m R_m<=sum_m R_m pointwise. QED.

The events W_m are nested. Although N>=R_m for every m, it does NOT
follow that N>=sum_m R_m. Equation (4) bounds this particular family
of lower certificates; it is NOT an upper bound for E N. Other explored
branches, other traps, and their interactions remain unaccounted for.
It also gives no uniform bound after conditioning on both roots lying
in infinite clusters. A proof using expected search cost must control
that actual conditional cost, rather than these selected certificates.

## 4. Verification and next mathematical obligation

`scripts/replay_search_barriers.py` runs 24 exact deterministic wall
searches (m=0,...,7 and beta=1,2,4), checks every returned open-path
certificate, and checks (1). It also exhausts the 4,096 configurations
of a ternary tree of depth two, verifying its exact Bernoulli mean and
the independent minimum's distribution at four rational parameters.
Exact rational arithmetic checks the factorization and series in (4).
The strengthened replay also verifies 88,208 explicit open four-cycle
certificates through queried edges and 32 finite-set boundary counts.
Results are in `search-barriers-replay.json`; the MSI run took about
3.6 seconds. These finite checks supplement the written proofs,
and do not establish their infinite statements by enumeration.

The deterministic detour shortcut is ruled out for these priorities,
but the single-wall probability calculation does not rule out a useful
expected-cost theorem. The outstanding task from
`fpbs-uniqueness-exploration-query-lower-bound` remains to prove an
upper bound on conditional queries per random-walk step that is strictly
smaller than its information lower bound under hypothetical collapse.
No such bound is asserted here.

The finite-branch approach was checked against
[Hermon--Hutchcroft, Proposition 2.1 and Section 2.1](https://arxiv.org/pdf/1904.10448).
Their lower bound for the loss term in a finite-cluster derivative
uses a positive constant at each fixed supercritical parameter; its
proof supplies no explicit lower bound for that constant. This
does not give the needed near-critical rate. More fundamentally,
Corollary 1.1 shows that for the current schedule, a query-cost estimate
must also control exploration inside the infinite part with no bridges.
It cannot charge all wasted queries to finite dangling branches.
