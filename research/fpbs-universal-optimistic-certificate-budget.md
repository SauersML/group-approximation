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
