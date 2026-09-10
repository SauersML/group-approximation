# Search geometry: a finite-query envelope and a geodesic-tie obstruction

Date: 2026-09-10. This develops the concrete searches from
`exploration-information.md`. It proves deterministic bounds and records
a small censored pilot. It does not establish an expected-cost bound
near p_c or resolve Benjamini--Schramm.

## 1. The shared search and its finite certificates

`scripts/exploration_search.py` implements the balanced two-ended search
used by both exact replays and the implicit-graph pilot. The priority of
a queued oriented edge (u,v) from side x toward endpoint y is

    depth_x(u)+1+beta d_G(v,y).                            (1)

Depth is fixed at first discovery. Equal priorities use insertion order
within each side. Fresh edge queries alternate sides; answers are cached
globally. Exhausting either frontier certifies disconnection. Meeting
discovered sets certifies connection. A query cap produces the separate
result `censored`, without asserting either outcome.

Successful searches return a path checked against queried open edges.
Negative results return a finite endpoint-containing set whose entire
boundary is checked to be queried and closed. These are finite certificates
valid for every completion of the remaining edge states. Censoring returns
no certificate. The exact transcript replay uses this same implementation.

## 2. The unit-weight search stays in a metric ellipse

Let x,y be connected in an arbitrary edge configuration of a connected
bounded-degree graph G. Let L be their shortest open-path length, and set

    E_L(x,y)={v: d_G(x,v)+d_G(v,y)<=L}.

**Proposition 1.** With beta=1 and no effective query cap, every edge
queried before termination has both endpoints in E_L(x,y). Therefore

    N <= |E(G[E_L(x,y)])| <= d |E_L(x,y)|/2               (2)

when G has maximum degree d. This is a deterministic statement about
query count, not just the length of the returned path.

**Proof.** First, every first-discovery depth from a side equals the
actual shortest open distance from that side. Suppose v were the first
counterexample, discovered at depth g greater than its open distance l.
Follow a shortest open path from the root to v and take its first still
undiscovered vertex w, with predecessor u. All previously discovered
depths are correct, so the queued edge (u,w) has priority at most
l+d_G(v,y), using the triangle inequality along the rest of that path.
It has not already been processed, since it is open and w is undiscovered.
This priority is strictly smaller than g+d_G(v,y), a contradiction.
Other-side queries can supply cached answers but do not invalidate this
argument; intersecting the discovered sets would terminate sooner.

Before termination, a shortest x-y open path always has a first
undiscovered vertex from each side, since discovering the other endpoint
would terminate. The same argument supplies a queued edge of priority
at most L on each side. Thus every processed edge (u,v) has priority
f=depth_x(u)+1+d_G(v,y)<=L. Its endpoint v satisfies
d_G(x,v)+d_G(v,y)<=f, while u satisfies the same inequality by
d_G(u,y)<=1+d_G(v,y). Both belong to E_L. The global cache prevents
duplicate fresh queries, proving (2). The finite-priority exhaustiveness
argument in `exploration-information.md` ensures termination. QED.

For G=T_4 x Z, let a be the tree distance between the endpoints and b
their absolute height difference. Put m=floor((L-a-b)/2). Then exactly

    |E_L(x,y)|=(a+2)(b+2)3^m-(a+b+2m+3).                 (3)

To see this, project a tree vertex onto the endpoint geodesic. At
distance r from that geodesic there are a+1 vertices when r=0 and
(2a+4)3^(r-1) when r>=1 (the latter formula also holds at a=0).
At that tree distance the height can be at distance at most m-r from
the interval between endpoint heights, allowing b+1+2(m-r) choices.
Summing over r and evaluating the geometric sums gives (3).

This formula identifies the difficulty of using (2) in expectation:
the excess open-path length enters exponentially. Neither this excess
nor its required moment is bounded here. Moreover, even m=0 leaves a
large rectangle when both endpoint coordinates differ.

## 3. Equal geodesic priorities can force quadratic work

**Proposition 2.** On T_4 x Z with every edge open, take endpoints with
tree distance ell and height difference ell, where ell>=1. The beta=1
search with insertion-order ties satisfies

    N >= ell(ell+1)/2-1.                                 (4)

Their graph distance is only 2ell. Consequently this schedule has no
universal deterministic O(distance) query bound, even in an all-open
configuration on a fixed nonamenable Cayley graph.

**Proof.** Proposition 1 confines the search to the geodesic rectangle:
the tree geodesic of length ell times the height interval of length ell.
Every forward edge in this rectangle has priority 2ell; backward edges
and edges leaving the rectangle have larger priority. Insertion-order
ties therefore make each side discover rectangle vertices in ordinary
breadth-first order by its depth.

At the first meeting, the two discovery depths sum to at least 2ell.
One side has consequently reached depth at least ell. Before its first
depth-ell discovery it has discovered every rectangle vertex of depth
less than ell, numbering ell(ell+1)/2. Except for its root, those
discoveries require fresh open-edge queries. An open edge already queried
by the other side would already connect the two discovered sets and
end the search; an edge already queried by the same side would already
have discovered its endpoints. This proves (4). QED.

**Proposition 3.** On any connected locally finite all-open graph, for
every fixed beta>1 the same search between distinct endpoints at graph
distance D uses at most 2D fresh queries.

**Proof.** Each side follows a single distance-decreasing geodesic until
termination. Inductively, at its current tip of depth j the remaining
distance is D-j. A forward edge has priority
beta D-(beta-1)(j+1), strictly below every pending edge from an earlier
tip. A nonforward edge at the current tip has larger priority as well.
Such a forward edge exists by the definition of graph distance. It is
open, so it discovers a new vertex at distance D-j-1, or meets the other
side. Cached answers can only reduce the fresh-query count. Each side
can make at most D such steps before reaching the other endpoint.
Summing proves the bound. QED.

These are algorithm calibrations at p=1, outside the parameter range of
the information lower bound. They do not assert any query rate for
p<1. In particular Proposition 2 is not a counterexample to the
percolation conjecture. T_4 x Z is nonamenable by the positive horizontal
tree boundary in each height slice.

## 4. A bounded implicit-graph pilot

The pilot uses the exact reduced-word geometry of Cay(F_2 x Z) with six
standard generators. A keyed BLAKE2b field supplies reproducible
pseudorandom edge labels; a separate seeded lazy walk supplies endpoints.
This is a numerical pilot, not a proof using genuinely independent
infinite random variables. The same field and endpoints are used for
the three schedules within each comparison.

It ran 12 seeds, walk lengths 16,48,96, parameters 0.35,0.60,0.90, and
beta=0,1,2, with a hard cap of 3,000 fresh queries per search: 324 searches
in total. Every returned path and closed-boundary certificate was checked.
The single MSI process completed the pilot in about 2.9 seconds.

At walk length 96, mean endpoint distance was about 20.7. Selected rows:

| p | beta | Connected | Disconnected | Censored | Mean observed queries |
|---|---:|---:|---:|---:|---:|
| 0.35 | 2 | 0 | 3 | 9 | 2257.1 |
| 0.60 | 0 | 0 | 0 | 12 | 3000.0 |
| 0.60 | 1 | 10 | 0 | 2 | 1143.1 |
| 0.60 | 2 | 12 | 0 | 0 | 266.4 |
| 0.90 | 0 | 0 | 0 | 12 | 3000.0 |
| 0.90 | 1 | 12 | 0 | 0 | 135.1 |
| 0.90 | 2 | 12 | 0 | 0 | 36.1 |

Observed-query means with censoring are truncated costs, not upper bounds
on expected completion cost. Completed searches do not determine whether
their endpoint cluster is infinite. No phase is assigned to these
parameters, and no critical parameter or asymptotic exponent is estimated.

For a concrete paired witness, seed 0 at p=0.60 and walk length 96 has
endpoint distance 21. The beta=2 search found a checked 27-edge path
after 80 queries, while beta=0 reached the cap. The result is saved in
`exploration-search-pilot.json` with all per-search records.

The next analytical candidate is beta>1, which avoids the proved
all-open tie obstruction and gave lower observed costs in this pilot.
The missing task remains a near-critical conditional expected-query
upper bound valid under hypothetical uniqueness on every Cayley graph.
The pilot and deterministic bounds do not supply it.

## 5. Exact verification

`scripts/replay_search_geometry.py` checks 684 all-open cases, 2,028
connected percolation cases for (2), and 64 exact product-ellipse counts
for (3). On all-open product rectangles of side length 32, the implemented
beta=1 and beta=2 schedules use 2,048 and 127 queries, respectively.
All finite checks passed on MSI; results are `search-geometry-replay.json`.

The shared engine also passes the exact likelihood and reachability replay
in `exploration-information-replay.json`. Its stopping rule now checks
both frontiers immediately, and separately tests censoring without
conflating it with disconnection. Cairn's current task validation is
`exploration-information-validation.json`. These checks verify finite
cases and dependency consistency, not the infinite mathematical proofs.
