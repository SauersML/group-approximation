---
rg: 2
id: fpbs-inverse-connectivity-matrix-not-laplacian
kind: claim
title: The inverse connectivity matrix need not have nonpositive off-diagonal entries
invalidates:
  - fpbs-dead-inverse-laplacian-expansion
artifacts:
  - research/artifacts/fpbs/responses/03_0908-195210.md
---

Bernoulli bond percolation on the four-cycle at p=1/2 has connectivity matrix T with adjacent entry 9/16 and opposite entry 7/16. Its inverse has (T^-1)_{0,2} = 16/1845 > 0. So the connectivity matrix is not the inverse of a graph Laplacian, and no expansion argument can be run through that sign property. Exact finite rational computation. This does not refute critical L2 boundedness and the four-cycle is not a counterexample to Benjamini-Schramm.
