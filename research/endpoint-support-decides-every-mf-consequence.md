---
rg: 2
id: endpoint-support-decides-every-mf-consequence
kind: route
title: Fix the marked core maps and compute normal closures by simple endpoint support
target: fixed-marked-mf-consequences-are-uniformly-polynomial
requires:
  - fixed-mf-quotient-kazhdan-extensions-realize-all-word-degrees
  - three-torsion-kazhdan-seam-is-just-non-mf
  - sturmian-seam-normal-and-mf-consequence-is-polynomial-time
artifacts:
  - research/artifacts/pestov91-fixed-mf-consequences-and-hidden-degrees-2026-09-13.md
---

Section 1 verifies that the binary endpoint systems and restricted marking
are independent of beta. Every MF map factors through their product.
Normal closure kills exactly the active simple factors; the remaining
product is LEF, proving both directions. The proof explicitly enumerates
interleaved endpoint windows and evaluates Laurent normal forms in cubic
field-operation cost. It does not substitute the differently coded graph
solver without changing its endpoint-language enumeration.
