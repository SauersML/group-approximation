---
rg: 2
id: surjunctivity-of-a-local-class-reflection-proof
kind: route
title: Realizations factor through the reflection, and the reflection is a member of the class
target: surjunctivity-of-a-local-class-is-reflection-kernel-membership
requires:
  - surjunctivity-is-axiomatized-by-rectangle-clauses
artifacts:
  - research/artifacts/metric-ultraproduct-bounded-width-closure-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

Artifact, Proposition 2.5.

- **The reflection is in `C`.** Finitely many quotients `F/M` separate any finite subset of `F/N_C`. The map into
  their product is injective on that subset and multiplicative, so `F/N_C` is locally embeddable into `C`.
- **If.** A realization `lambda` of `D` in a group of `C` has kernel `M ⊇ N_C`. So it kills every reverse word in
  `N_C`, which contradicts realization. By `surjunctivity-is-axiomatized-by-rectangle-clauses`, every group in `C` is
  surjunctive.
- **Only if.** `F/N_C` is surjunctive, so its canonical labelling kills some reverse word.

**Verification.** `w3-vf-positive` passed this route (Section 10.3 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`).
