# Replanning optimistic paths as a percolation query algorithm

This replaces the scalar-priority schedule in the current search attempt
with a different candidate. It proves connected-case correctness, an
exact discovered-vertex accounting identity, and a linear query bound
on the wall configurations that defeated the earlier schedule. The
Bernoulli bound needed for the universal Benjamini--Schramm theorem is
still unproved.

The algorithm is a version of the established lazy shortest-path
framework of [Dellin--Srinivasa](https://arxiv.org/abs/1603.03490).
The forward selector and its finite-graph analysis also appear in
[Haghtalab et al.](https://arxiv.org/pdf/1710.04101). No novelty of the
search framework is claimed. The proofs below give the precise
infinite-graph and wall statements used in this investigation.

Status checked on 2026-09-10: [Chu, version 2 dated September 5,
Section 1.B](https://arxiv.org/html/2608.06644#S1.SS2) still presents
the general nonamenable threshold separation as conjectural. The
results here do not claim to resolve it or exhaust the literature.

## 1. The algorithm and its two budgets

Keep a global cache of queried open and closed edges. Treat every
unqueried edge as open for planning purposes. Repeatedly:

1. Find a shortest source-to-target path in the graph with the known
   closed edges removed. Among equal-length paths, choose one with
   the fewest unqueried edges, then break remaining ties deterministically.
2. Test unqueried edges along that path in order from the source.
   On the first closed answer, replan. If the whole path is verified,
   return its open-path certificate.

The implementation is `optimistic_search` in `scripts/exploration_search.py`.
Its planner uses lexicographic A*: path cost is (length, number of
unqueried edges), and the heuristic is (ambient distance to target, 0).
This heuristic is admissible and consistent after deleting known closed
edges: the ambient distance changes by at most one across any edge,
and its second coordinate is zero. The secondary preference for fewer
unknown edges is part of the specified algorithm, not an optional tie rule.

Only `read_edge` obtains percolation information. Planning inspects graph
geometry and the cache. Geometry is free in the mathematical query model,
as in the previous exploration notes, but costs real computation in the
implementation. Accordingly fresh queries and planner expansions have
separate finite caps. Reaching either cap returns `censored`, identifying
which cap was reached. A finite exhausted optimistic source component
gives a checked closed-boundary certificate and `disconnected`.

Without a planning cap, search in an infinite optimistic component need
not terminate when no optimistic source-to-target path exists. We do
not claim a total infinite-graph decision procedure. Finite caps always
give a bounded experiment, which is enough to apply the strong converse
in `query-strong-converse.md`.

## 2. Certified growth and connected-case correctness

Let Q be the graph consisting of the source and all queried-open edges.
Let N be the number of fresh queries and U the number of open answers.

**Proposition 1.** At every stage, Q is a tree containing the source,
and every fresh query has exactly one endpoint in Q. Hence

    |V(Q)| = U+1.                                         (1)

For any bounded run under iid Bernoulli(q), including either form of
censoring,

    E_q N = E_q[|V(Q)|-1]/q.                              (2)

**Proof of the deterministic invariant.** Maintain the stronger invariant
that for every vertex v in Q, its tree path from the source is a shortest
path to v in the current optimistic graph. This holds initially.
Closing an edge cannot invalidate a known-open tree path or decrease
an optimistic distance, so it preserves this invariant for existing
vertices.

Consider the first unqueried edge (u,v) on the current candidate path.
Its prefix through u is known open, so u belongs to Q. Every prefix
of a shortest path is shortest to its endpoint. If v already belonged
to Q, replacing the prefix through (u,v) by the known tree path to v
would preserve total length and strictly reduce the number of unknown
edges. A repeated vertex in the replacement walk would yield an even
shorter path after deleting a loop, also contradicting shortestness.
Thus the replacement contradicts the prescribed tie rule, and v is
outside Q.

An open answer therefore appends a new vertex and preserves the stronger
invariant, since this candidate prefix is an optimistic geodesic. The
same candidate remains optimal after this answer: it loses one unknown
edge, while every competitor loses either zero or one. Thus testing
the rest of its prefix without replanning preserves the argument.
A closed answer triggers the next plan and was already handled above.
This proves the invariant and (1).

**Proof of (2).** At each requested fresh query the answer still has
conditional probability q of being open. For a bounded stopping time,
sum these conditional expectations to get E_q U=q E_q N, and use (1).
This is an unconditional identity. Conditioning on both endpoint clusters
being infinite does not preserve fresh Bernoulli(q) answers, so (2) must
not be asserted under that conditioning without a new argument. QED.

**Proposition 2.** If the endpoints are connected by an open path and
their shortest open distance is L, the uncapped algorithm terminates
and returns a shortest open path. All queried edges have both endpoints
in the finite ambient ellipse

    E_L={v:d(source,v)+d(v,target)<=L}.

In particular, on a graph of maximum degree d,

    N <= |E(G[E_L])| <= d|E_L|/2.                         (3)

If C is the number of closed queries in that run, also

    N <= L(C+1).                                         (4)

**Proof.** A fixed shortest actual open path survives every known-closed
deletion. Every optimistic candidate consequently has length at most L.
Every vertex of such a path belongs to E_L by the ambient triangle
inequality. The ellipse is finite by local finiteness, and no edge is
queried twice. Each failed candidate produces one new closed query.
There can therefore be only finitely many failures before a fully open
candidate is found. Each planning call also finishes: a candidate of
length at most L exists, and only finitely many states have first A*
priority coordinate at most L. The finite secondary costs and stale-entry
checks do not change this finiteness. The successful candidate is shortest
in a graph containing the true open graph, hence has length exactly L.
This proves correctness and (3). Each of the C failed candidates and
the final successful candidate uses at most L fresh queries, giving (4).
QED.

This gives a finite bound, not the near-critical quantitative estimate:
|E_L| may be exponentially large in the excess of open distance over
ambient distance. Equation (2) makes the still-missing quantity more
concrete: the algorithm must limit the number of certified vertices it
explores, including vertices in regions with no bridges.

## 3. An exact linear wall bound

Use the configuration of `search-barriers.md`: the endpoints are
(x,0),(y,0) across a tree edge xy in T_4 x Z; its copies at |z|<=m
are closed and every other edge is open.

**Proposition 3.** The algorithm above uses exactly

    N=5m+4=(5L-7)/2,    L=2m+3.                          (5)

**Proof.** At every round the only known closed edges are copies of xy.
Let r be the smallest absolute height with an untested copy. Every
optimistic path must cross xy at some available height and has length
at least 2r+1. Equality is achieved by going vertically on the x side,
crossing once, and returning vertically on the y side. Any additional
tree motion, extra crossing, or vertical reversal adds length, so every
optimistic geodesic has exactly this form at an available height of
absolute value r.

The algorithm first tests height zero, then both signs of each height
1,...,m in some order, then one sign at height m+1. Each failed path
is read only through its closed crossing, so no vertical edge on the
y side is queried before the final successful path. Across all rounds,
the x-side vertical queries reach height m in both directions and one
extra step in the successful direction, giving 2m+1 such open queries.
There are 2m+1 closed crossings, one open crossing, and m+1 y-side
vertical queries on the successful path. Their sum is 5m+4. All
queries are distinct after caching. QED.

Thus the earlier exponential wall obstruction is specific to its
scalar-priority schedule. At m=7, the new search uses 39 fresh queries,
whereas the previously replayed beta=2 schedule used 58,990. This does
not imply an efficient Bernoulli search on every Cayley graph. In
particular the planner still performs 39,380 expansions in this m=7
run: edge information and planning work are distinct costs.

## 4. Finite verification and a deliberately bounded pilot

`scripts/replay_optimistic_search.py` passed 93 finite cap cases over
3,300 configurations and 386 terminal transcripts. It checks returned
paths and cuts, exact shortest-path length on success, ellipse containment,
the tree-growth invariant at every fresh query, exact transcript cylinder
probabilities, and (2) with rational arithmetic. Separate cases verify
query censoring, planning censoring, and coincident endpoints.

Eight exact wall runs, m=0,...,7, verify (5) and all returned certificates.
A further 16-run T_4 x Z pilot uses the same keyed BLAKE2b field and
independent walk seeds as the earlier pilot, now with four seeds, walk
lengths 48 and 96, q=0.60 and 0.90, a 400-query cap and an 8,000-expansion
planning cap. At q=0.90 all eight runs return checked paths. At q=0.60,
three return paths and five reach the planning cap. None of these five
is classified as disconnected.

For seed zero at q=0.60 and walk length 96, the endpoint distance is
21 and the search certifies a 27-edge path after 59 fresh queries and
4,060 planner expansions. These are finite pseudorandom observations,
not iid infinite-graph theorems, phase estimates, or infinite-cluster
membership tests. The combined MSI replay took about 1.7 seconds;
results are in `optimistic-search-replay.json`.

## 5. The remaining universal estimate

The published finite-graph upper bound in
[Haghtalab et al., Theorem 3](https://arxiv.org/pdf/1710.04101) is of
order (|V|+log(1/delta))/q for connective selectors. Here |V| is the
number of graph vertices; it is not the ambient random-walk length.
An exponentially large ellipse or ball cannot be substituted for |V|
and then treated as a linear-size search region. Their instance-wise
optimality theorem also permits a selector chosen for the realized
configuration, which is not an admissible source of unqueried information
in our entropy comparison.

To finish the current Benjamini--Schramm route, one still must prove
under hypothetical threshold collapse that some admissible capped search
finds connections between o and X_n with sufficiently large probability
below the information budget in `query-strong-converse.md`. The new
algorithm overcomes the particular deterministic wall, but neither
(2)--(4) nor the pilot provides that bound. Seeking a shortest open
path may itself impose more work than finding any open path; a proof
may need a different selector or a relaxed path objective. The main
claim remains OPEN.

Cairn now represents this obligation explicitly as the OPEN claim
`fpbs-universal-optimistic-certificate-budget`. The conditional route
`fpbs-universal-optimistic-certificate-route` requires that construction,
the certified-growth theorem, and the query strong converse; it targets
`fpbs-benjamini-schramm-universal`. The contradiction in the route is
complete only after the budget premise is proved. A prose cross-link
alone would not create this dependency in Cairn's computed frontier.
