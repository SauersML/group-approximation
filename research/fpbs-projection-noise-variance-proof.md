---
rg: 2
id: fpbs-projection-noise-variance-proof
kind: route
title: Combine the idempotent merger loss with Hilbert-valued product variance
target: fpbs-projection-noise-variance-identity
requires:
  - fpbs-cluster-merger-projections
artifacts:
  - research/artifacts/fpbs/projection-resolvent.md
---

Section 1 proves the product variance expansion directly for P_omega f,
uses P_omega^2=P_omega, and identifies the coordinate variance sum with
-p(1-p)Q_p' because each merger loss Delta satisfies Delta^2=Delta.
Subtracting the expansions yields the exact positive remainder for all
test vectors, hence the matrix identity by polarization.
