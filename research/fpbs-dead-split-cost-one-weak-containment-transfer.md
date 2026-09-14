---
rg: 2
id: fpbs-dead-split-cost-one-weak-containment-transfer
kind: route
title: Transfer quotient-split cost one to the Bernoulli shift by weak containment
target: fpbs-normal-subgroup-bounded-cost-fixed-price-one
requires: []
artifacts:
  - research/artifacts/fpbs/docs/normal-subgroup-fixed-price.md
---

Dead: the attempt takes a quotient-split action of cost one, from
fpbs-quotient-split-actions-have-cost-one, and argues that it is weakly
contained in the Bernoulli shift. For finitely generated groups, cost is
monotone under weak containment, so the Bernoulli shift would have cost one,
and Abert--Weiss maximality would then give fixed price one.

The weak containment fails whenever the normal subgroup is nonamenable
(fpbs-quotient-split-not-bernoulli-contained). The nontrivial factor fixed by
N produces an N-invariant vector in L^2_0, while the Bernoulli Koopman
representation restricted to N is contained in a multiple of the regular
representation of N. When N is infinite and amenable the conclusion was
already known, so the route yields nothing new in either case.
