---
rg: 2
id: fpbs-bounded-query-connection-strong-converse-proof
kind: route
title: Pad adaptive queries and combine their likelihood moment with critical spectral decay
target: fpbs-bounded-query-connection-strong-converse
requires:
  - fpbs-critical-walk-correlation
artifacts:
  - research/artifacts/fpbs/query-strong-converse.md
---

Sections 1 and 2 supply the proof. Padding with fresh queries gives
exactly m independent Bernoulli answers conditional on the seed.
Holder's inequality bounds event transfer by the explicit Renyi
divergence. A path certificate at c has probability at most rho^n.
Continuity of D_alpha at alpha=1 yields the strict linear-budget
threshold without expected-cost or uncapped termination assumptions.
