---
rg: 2
id: stw99-lxxvi-one-dimensional-graph-limit-proof
kind: route
title: Pass the finite-graph first-factor isomorphisms through inverse limits and then to the open ideal
target: stw99-lxxvi-one-dimensional-simple-fiber-cu-regularity
requires:
  - stw99-lxxvi-finite-graph-compact-core-cu-regularity
  - stw99-lxxvi-cu-regularity-passes-to-inductive-limits
  - stw99-lxxvi-cu-regularity-passes-to-ideals-and-quotients
artifacts:
  - research/artifacts/stw99-lxxvi-one-dimensional-simple-fiber-audit-2026-09-05.md
---

For compact `X`, the one-dimensional Freudenthal representation gives
`X=lim_inverse X_n` with finite graphs `X_n` and surjective bonding maps.
Consequently `C(X,D)=lim_direct C(X_n,D)`. The first-factor maps commute
with these connecting *-homomorphisms. The finite-graph compact-core
theorem makes each first-factor Cu map an isomorphism, and continuity of
Cu makes the actual limit map an isomorphism.

For noncompact `X`, its one-point compactification is compact metrizable
of dimension at most one. One direct dimension check uses a compact
exhaustion of `X` and the singleton at infinity: they are a countable
closed cover of the compactification, so the metric closed-sum theorem
preserves the dimension bound. Apply the compact result there.
`C_0(X,D)` is the ideal of sections vanishing at infinity, and concrete
Cu regularity passes to this ideal. Purity in the pure-fiber corollary
follows separately from the continuous-function purity theorem.
