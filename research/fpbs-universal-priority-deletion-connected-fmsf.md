---
rg: 2
id: fpbs-universal-priority-deletion-connected-fmsf
kind: claim
title: Universal short-cycle priority deletion stays connected and retains the free minimal spanning forest
distinct_from:
  fpbs-priority-finite-rank: that records the bare induction principle for the earlier construction's selected relator supports; this one is the universal scheme H_{R,M} on every locally finite Cayley graph, with the explicit replacement-distance bound and the spanning-forest inclusion
  fpbs-tfl-metric: that is the replacement-distance formula for the specific torsion-free relator family and its finite-radius iid sparsifier; this one is the parameter-free bound for independent uniform edge labels quantised to M levels
artifacts:
  - research/artifacts/fpbs/responses/47_0909-191353.md
  - research/artifacts/fpbs/docs/fixed-price-finite-priority.md
---

Give the unoriented edges of a locally finite Cayley graph independent uniform labels U_e and quantise them to r_M(e)=1+floor(M U_e). For R>=3 delete e exactly when some cycle of length at most R through e has all its other edges of strictly smaller priority, and call the result H_{R,M}. Then H_{R,M} is connected for every R and M, by induction on the finitely many priority levels, with the deterministic bound d_{H_{R,M}}(x,y) <= (R-1)^{M-1} d_G(x,y). The same comparison shows F is contained in H_{R,M} for the free minimal spanning forest F of the underlying continuous labels, so half the expected root degree of H_{R,M} is at least that of F; along R=k, M=2^k the two agree in the limit.

Status records a written deduction, not independent validation. Response 47 reports 6,318 finite configurations and 12,636 assertions passing for the connectivity and inclusion calculations; those test the finite accounting only.
