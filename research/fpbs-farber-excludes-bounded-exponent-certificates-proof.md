---
rg: 2
id: fpbs-farber-excludes-bounded-exponent-certificates-proof
kind: route
title: The trivial kernel of the boundary action gives residual finiteness, and restricted Burnside makes bounded-exponent subgroups locally finite
target: fpbs-farber-excludes-bounded-exponent-certificates
requires:
  - fg-rf-bounded-exponent-groups-are-finite
artifacts:
  - research/artifacts/fpbs/counterexample-heretic-w5-2026-09-17.md
---

The written proof is Section 2 of the linked note.

1. The intersection of the cores of the chain fixes every boundary point.
   Essential freeness on a probability space forces it to be trivial.
2. A finitely generated subgroup of a bounded-exponent subgroup is residually
   finite, finitely generated and of bounded exponent, hence finite.
3. `<g> <= C_M(g)` bounds every order by `n`, so the exponent divides `n!`.
4. Take `M = N = G`.

This is a written deduction, not a formal verification.
