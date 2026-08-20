---
rg: 2
id: mixed-cnot-joint-exit-first-hit-transducer-via-endpoints
kind: route
title: Use the two flag signs as shared marginals and charge the impossible rank-one triangle
target: mixed-cnot-joint-exit-first-hit-transducer
requires:
  - mixed-central-router-adjoins-without-collapsing-packet
  - robust-rank-one-endpoint-marginal-floor
  - free-root-sign-atoms-transport-with-linear-hs-loss
  - free-root-first-detection-eigenvectors-localize-exactly
  - product-clock-synchronizes-fanizza-and-e5
  - mixed-cnot-endpoint-failure-relator-certificate
---

Use the router flag `d` before and after its automorphism as the two endpoint
bits.  On `QF`, `(MCR5)` supplies the common rank-one source fiber and the
exact sign map `(sigma,epsilon)->(epsilon sigma,epsilon)`.  Install three
stable-letter contexts with the `(00),(01),(11)` endpoint reuse pattern of
`robust-rank-one-endpoint-marginal-floor`.  Couple only the crossed-context
failure to the top E5 hard root; the two diagonal failures are returned to
the active chart.

The endpoint atom transport theorem bounds marginal drift by a polynomial
sum of root covariance defects.  What is not yet proved is the sparse
group-relator certificate identifying the three contextual failures with the
active/exit projections in `(MCF1)` while leaving the allowed `K=+1` sector
zero-energy.  That certificate, not another finite rank search, is the sole
content still open in this route.
