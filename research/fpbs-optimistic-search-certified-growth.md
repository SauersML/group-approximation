---
rg: 2
id: fpbs-optimistic-search-certified-growth
kind: claim
title: Forward optimistic shortest-path queries grow a certified tree and terminate on connected pairs
artifacts:
  - research/artifacts/fpbs/optimistic-search.md
---

The search replans a shortest path after each closed answer, preferring
fewer unqueried edges among equal-length paths, and queries from the
source. Every query crosses the current certified tree boundary and
every open answer appends one vertex. For any bounded run,
E_q N=E_q(|V(Q)|-1)/q. If shortest open distance is L, the uncapped
search terminates with a shortest open path and queries only edges
inside the ambient ellipse E_L, with N<=d|E_L|/2 and N<=L(C+1).
No total decision procedure on disconnected infinite pairs or conditional
infinite-cluster Wald identity is asserted.
