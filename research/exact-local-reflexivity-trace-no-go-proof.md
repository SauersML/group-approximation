---
rg: 2
id: exact-local-reflexivity-trace-no-go-proof
kind: route
title: Use the exact sofic non-MF witness and pull an MF reduced trace back to the full algebra
target: exact-local-reflexivity-does-not-promote-hyperlinear-traces
requires:
  - exact-stably-finite-non-mf-reduced-group-algebra
  - sofic-non-mf-witness
  - regular-character-mf-trace-implies-group-mf
artifacts:
  - research/artifacts/cstar-regularity-trace-promotion-audit-2026-08-23.md
  - GroupApproximation/Analysis/MFTracePullback.lean
---

Let `W` be the common witness in the first two prerequisites.  Its reduced
algebra is separable and exact and its canonical trace is faithful.  Soficity
gives a trace-preserving embedding `L(W)->R^omega`, so the reduced canonical
trace is hyperlinear.  If that trace were MF, the proved pullback theorem for
MF traces would make the canonical trace on `C^*(W)` MF; the recognition
theorem would then make `W` operator MF, contradicting `sofic-non-mf-witness`.
Finally exact C-star algebras are locally reflexive.
