---
rg: 2
id: fpbs-relative-cycle-retraction-rounding-proof
kind: route
title: Bound path residual by the contractively transported certificate and apply the cost identity
target: fpbs-relative-cycle-retraction-rounding
requires:
  - fpbs-cycle-retraction-contractive-transport
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
  - research/artifacts/fpbs/docs/relative-cycle-iteration.md
---

The transport theorem gives a positive contraction K' with
c(J)=c(H)-Tr(K)+Tr(K')-eta, where eta>=0 and
Tr(K')<=Tr(R K R-star). Dropping eta gives the general path bound.
For the relative operator, its defining trace identity substitutes
c(Phi) for c(H)-Tr(K), giving the relative version.

Section 7 of the exchange artifact retains the direct projection
proof and checks the bounded bridge construction. Sections 1--3
of the iteration artifact prove why the smaller transported
certificate, rather than the raw path image, is valid for iteration.
