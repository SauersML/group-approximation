---
rg: 2
id: one-dimensional-periodic-address-proof
kind: route
title: Extract a de Bruijn cycle and represent it on one finite cyclic orbit
target: one-dimensional-address-rules-have-periodic-models
requires:
  - baumslag-address-geometric-stationary-profile
  - periodic-bs-clock-defeats-spectral-first-hit-checksum
---

A nonempty one-dimensional shift of finite type gives a bi-infinite path in
its finite overlap graph.  Repetition of a forward vertex produces a directed
cycle, whose infinite repetition is a periodic admissible configuration.
Diagonal color projections on the cyclic orbit and the cyclic shift satisfy
all PVM, covariance, and forbidden-window rows exactly, proving
`(OPA1)--(OPA3)`.  Equivariance gives `(OPA4)`, which contradicts either
infinitely many positive pairwise orthogonal translates or the periodic
iteration of `(OPA5)`.  The two required claims record the corresponding
periodic exact models for the Baumslag finite-field and Baumslag--Solitar
spectral address variants outside the literal finite-alphabet SFT syntax.
