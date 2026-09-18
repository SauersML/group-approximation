---
rg: 2
id: fpbs-universal-optimistic-certificate-budget
kind: claim
title: Threshold collapse would permit optimistic connection certificates below the information budget
artifacts:
  - research/artifacts/fpbs/optimistic-search.md
  - research/artifacts/fpbs/query-strong-converse.md
---

OPEN CONSTRUCTION. For every locally finite Cayley graph G of a
nonamenable group, put c=p_c(G), rho=the lazy-walk operator norm, and
lambda=-log rho. Under the hypothesis p_c(G)=p_u(G), there exist
q in (c,1), b with 0<b<lambda/k(q,c), and finite deterministic
planning caps M_n such that the optimistic search of
fpbs-optimistic-search-certified-growth, from o to the independent
lazy-walk endpoint X_n, with query cap floor(b*n) and planning cap M_n,
satisfies

    limsup_{n->infinity} n^(-1) log P_q(search returns a path) = 0.

Here k(q,c)=q log(q/c)+(1-q) log((1-q)/(1-c)), and log 0=-infinity.
All schedules, tie rules and caps are fixed independently of the
percolation answers. The parameters and caps may depend on G and q.
This proposition has no proof route. Its conditional hypothesis does
not permit assuming the claimed construction without proof.

## Attempts

Optimistic replanning overcomes the scalar-priority wall obstruction
and its queried-open edges form a certified tree. Bounded runs obey
E_q N=E_q(|V(Q)|-1)/q. These facts do not bound |V(Q)| in the required
regime. The deterministic ellipse can be exponentially large, the
finite-graph LazySP estimate counts all graph vertices, and the bounded
pseudorandom pilot neither determines infinite-cluster membership nor
establishes an asymptotic probability. What remains is an actual
Bernoulli estimate under collapse, valid on every prescribed Cayley graph.

**Equivalence diagnosis (b-t-optcert, swarm-0917, 2026-09-17).**
Established node: `fpbs-certificate-budget-premise-is-equivalent-to-goal`.
Artifact: `research/artifacts/fpbs-certificate-budget-premise-equivalence-2026-09-17.md`.

The strong converse `fpbs-bounded-query-connection-strong-converse` has no
collapse hypothesis. The conclusion of this premise, success rate 0 below
lambda/k(q,c), is therefore false on every nonamenable Cayley graph, at
every q in (c,1), for every admissible algorithm. This premise holds for G
exactly when p_c(G)<p_u(G), so it is the goal restated. The route
`fpbs-universal-optimistic-certificate-route` adds no decomposition.

The diagnosis applies to every admissible selector, relaxed path objective,
cap, tube reader and waypoint scheme, and to the weakened conclusions:
subsequences, conditioning on infinite endpoints, and expected cost.

Dead class: derivations collapse => Psi => cheap certificates in which Psi
is realized at some existing supercritical triple. Examples of such Psi are
uniqueness, fixed-supercritical tails, anchored expansion and tube bounds.
Each dies at the leg Psi => cheap, against the converse exponent eta>0.

Do not spend further work designing search algorithms for this hole. Any
proof must extract from collapse a property that holds at no supercritical
parameter of any nonamenable Cayley graph. That property already refutes
collapse without queries.
