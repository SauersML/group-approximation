---
rg: 2
id: fpbs-infinite-contact-zero-relative-cost-proof
kind: route
title: Sample shared connectors and derandomize finite connection tests with paid tails
target: fpbs-infinite-contact-zero-relative-cost
requires: []
artifacts:
  - research/artifacts/fpbs/docs/shared-component-repair.md
---

Section 1 supplies the direct proof. Each infinite contact has
infinitely many distinct oriented starting vertices, so sparse
independent vertex marking connects it almost surely. Countably
many contacts suffice per orbit. For a finite prefix of H-demands,
choose finitely many successful path tests, approximate their marks
by independent colors of separating measurable partition atoms,
and repair every failure directly. Append all remaining H-maps,
paying their ordinary tail cost. Averaging yields repairs of cost
at most epsilon c(H)+eta for arbitrary positive epsilon and eta.

Sections 3--4 prove the two audited subsidiary assertions. A finite
cut vector is orthogonal to the finite cycle space and hence lies
in the kernel of a dominated positive cycle contraction; the
determinantal inclusion formula makes deleting the whole cut a
null event. For the recursive parallel-path graph, every cut crosses
infinitely many edge-disjoint detours, while the exact series-parallel
percolation recurrence stays at most one half at p=one quarter.
Every connecting path has finite depth, justifying passage to the
union. Imported for the cut audit: the defining determinantal
inclusion probabilities from Lyons, linked in the artifact.

These are written deductions, not formal proof verification.
