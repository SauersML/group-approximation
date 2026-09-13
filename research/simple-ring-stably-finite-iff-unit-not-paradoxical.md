---
rg: 2
id: simple-ring-stably-finite-iff-unit-not-paradoxical
kind: claim
title: A countable simple unital ring is stably finite iff [R] is not paradoxical in V(R) iff V(R) has a state normalized at [R]
distinct_from:
  kmp-plain-paradox-groupoid-dichotomy: that is the analytic statement for simple groupoid C*-algebras (stable finiteness iff a state on the type semigroup); this is the purely algebraic statement for simple rings and V(R).
artifacts:
  - research/artifacts/un-middle-stable-paradox-threshold-2026-09-13.md
---

Let `R ≠ 0` be a countable simple unital ring. The following are equivalent:
- (a) `M_n(R)` is directly finite for every `n`;
- (b) `[R]` is not paradoxical in `V(R)`;
- (c) `V(R)` admits a state `ν` with `ν([R]) = 1`.

Moreover, the paradoxical level `p(R) = min{n : (n+1)[R] ≤ n[R]}` equals `min{n : M_n(R) not directly finite}`.
Together with `paradoxical-ring-el-n-full-mf-radical-from-twice-level`: if `R` is not stably finite, then `EL_N(R)` has
full MF radical for `N ≥ 2p(R)`.
