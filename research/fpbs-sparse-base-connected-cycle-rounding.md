---
rg: 2
id: fpbs-sparse-base-connected-cycle-rounding
kind: claim
title: Sparse base regions admit connected surgery and rounding of supported relative cycle certificates
artifacts:
  - research/artifacts/fpbs/docs/sparse-base-surgery.md
---

Fix an exact countably infinite group, its Bernoulli action X, a finite
symmetric label set S and eta>0. There exist delta>0 and k<infinity
such that any simple S-subgraphing H and base set A with mu(A)<=delta
admit a base-measurable edge cut F in H[A] of cost at most eta mu(A),
strictly less when mu(A)>0, leaving components of size at most k.
Graphing statements are modulo invariant null sets.

If H generates, replacing those components by trees and retaining F
and all exterior edges preserves generation. If additionally
0<=K<=P_Z(H) has range supported on H[A], the resulting J satisfies
c(J)<=c(H)-Tr(K)+eta mu(A). For a relative source certificate this
gives C(X)<=c(Phi)+eta mu(A).

The proof uses actual cut rank, not an assumption that small exterior
trace has small rank. It does not construct sparse support for arbitrary
relative certificates, cover nonexact groups, or resolve Fixed Price.
