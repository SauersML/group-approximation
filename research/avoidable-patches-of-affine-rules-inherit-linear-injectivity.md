---
rg: 2
id: avoidable-patches-of-affine-rules-inherit-linear-injectivity
kind: claim
title: A rule on at least three symbols that agrees with an affine rule wherever a fixed symbol is absent is injective only where the linear part is injective
distinct_from:
  low-degree-strict-pairs-have-one-sided-linear-parts: that extracts one-sided inverse pairs from the linear parts of low-degree strict pairs through reduced polynomials; this needs no degree bound and no decoder, and transfers injectivity from a patched rule to its linear part by avoiding one symbol.
artifacts:
  - research/artifacts/small-memory-balance-census-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `avoidable-affine-patch-injectivity-proof`.

**Proposition.** Let `A = F_q` with `q >= 3`. Let `lambda = sum_m c_m x_m + c_0` be an affine rule
with linear part `lambda_0`, and let `mu` agree with `lambda` on every pattern in which a fixed
symbol `s` does not occur. If the automaton of `mu` is injective over `G`, then so is the linear
automaton of `lambda_0`. So either `G` carries a linear strict automaton, or `sum_m c_m m` is a
unit of `F_q[G]`.

**Use.** An unbalanced patch of this kind gives a nonlinear counterexample over `G` only when its
linear part is a unit of `F_q[G]`. Example: the rigid ternary rule `x - y + z` patched at `(0,2,2)`
needs `1 - a + b` to be a unit.

**Boundary.** Two symbols leave no room to avoid a symbol.

Artifact, Section 5.1.
