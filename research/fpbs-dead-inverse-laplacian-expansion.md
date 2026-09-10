---
rg: 2
id: fpbs-dead-inverse-laplacian-expansion
kind: route
title: Prove critical L2 boundedness by treating the connectivity matrix as an inverse Laplacian
target: fpbs-benjamini-schramm-universal
requires:
  - fpbs-inverse-connectivity-off-diagonal-nonpositive
artifacts:
  - research/artifacts/fpbs/responses/03_0908-195210.md
---

Dead: the attempt bounds the critical connectivity operator by exhibiting its inverse as a graph Laplacian and applying edge expansion, then feeds the resulting bound into the established L2 criterion. Its sign lemma is false: on the four-cycle at p=1/2 the exact inverse has a strictly positive off-diagonal entry (fpbs-inverse-connectivity-matrix-not-laplacian). The implication from critical L2 boundedness to a nonuniqueness interval survives; only this proposed proof of the boundedness input dies.
