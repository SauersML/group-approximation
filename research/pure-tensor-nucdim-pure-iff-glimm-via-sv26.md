---
rg: 2
id: pure-tensor-nucdim-pure-iff-glimm-via-sv26
kind: route
title: Supply the Seth--Vilalta hypotheses by the two transfer theorems
target: pure-tensor-nucdim-factor-pure-iff-global-glimm
requires:
  - nucdim-factor-transfers-m-comparison
  - nucdim-factor-transfers-bounded-divisibility
  - sv26-bounded-divisibility-dimension-reduction
  - sv26-global-glimm-gives-two-color-splitting
artifacts:
  - research/artifacts/nucdim-factor-comparison-divisibility-2026-09-16.md
---

Artifact Section 9 (Corollary E').

A pure algebra has almost unperforated and almost divisible Cuntz semigroup.
By `nucdim-factor-transfers-m-comparison`, `Cu(C)` has `m`-comparison.  By
`nucdim-factor-transfers-bounded-divisibility`, for every `N >= 1` and
`x' << x` in `Cu(C)` there is `y` with `x' << N y << 2(m+1) x`.  These are
exactly the standing hypotheses (with `M = 2(m+1)`) of
`sv26-bounded-divisibility-dimension-reduction` and
`sv26-global-glimm-gives-two-color-splitting`.

- 2 implies 3: `sv26-global-glimm-gives-two-color-splitting`, with
  `L = 2(m+1)(M_1+2)` and `M_1 = 2M^3`.
- 3 implies 1: item 2 of `sv26-bounded-divisibility-dimension-reduction`.
- 1 implies 2: item 3 of `sv26-bounded-divisibility-dimension-reduction`.
