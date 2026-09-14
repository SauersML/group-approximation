---
rg: 2
id: lef-finite-simple-limit-sl-n-from-sl-3n-statement
kind: route
title: The SL_3N marked-limit characterization of LEF groups gives the SL_N version, since the SL_3N are among the SL_N
target: lef-iff-subgroup-of-simple-kazhdan-finite-simple-limit
requires:
  - lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple
---

**Subsumption** (duplicate D1: sk-verify-7 `research/artifacts/sk-review-7-2026-09-13-part3.md`, sk-verify-8
`research/artifacts/sk-review-8-2026-09-13-part1.md`). The two claims state the same theorem. sk-strong-6 derived one
with configuration-space models on `2^(Q_n)`; sk-strong-8 derived the other with view models. Each keeps its own proof
route.

Let `Γ` be finitely generated.
- (1) ⇒ (2). If `Γ` is LEF, `lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple` gives an infinite finitely
  generated simple Kazhdan group `G ⊇ Γ`, a finite generating set `S_G` and `N_k → ∞`, such that
  `(SL_(3N_k)(F_2), images of S_G) → (G, S_G)` in the space of marked groups with expander Cayley graphs. With
  `N'_k = 3N_k`, the same sequence presents `G` as a marked limit of finite simple groups `SL_(N'_k)(F_2)` whose Cayley
  graphs form expanders. That is statement (2) of the target.
- (2) ⇒ (1). A marked limit of finite groups is LEF: a ball of the limit agrees with a ball of a finite group from the
  sequence, which gives an injective map preserving products that stay in the ball. LEF passes to subgroups, so `Γ` is
  LEF.
