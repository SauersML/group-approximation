---
rg: 2
id: antipodal-one-sided-group-shift-configurations-are-walls
kind: claim
title: A group shift with nonzero configurations supported in two opposite half-planes has wall certificates at every scale and is not quantum rigid
distinct_from:
  positive-entropy-sft-crossed-products-are-not-fp: that builds walls from entropy by pigeonhole; this builds them for zero-entropy group shifts by superposing two one-sided configurations, the analogue of an antipodal pair in the Bieri–Strebel invariant.
  sft-wall-rigidity-iff-idempotent-commutator-ideal: that characterizes walls as the first-order obstruction; this identifies the walls of algebraic shifts with antipodal one-sided directions.
artifacts:
  - research/artifacts/quantum-rigidity-group-shifts-and-gluing-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `X ⊆ (F_p^m)^(Z^2)` be a group shift, and `v` a direction with nonzero
configurations `c_+, c_- ∈ X`. The support of `c_+` lies in `{<n, v> > 0}`, and that of `c_-` in `{<n, v> < 0}`.
1. For every `D`, `X` is not `D`-wall-rigid. Superposing translates of `c_+` and `c_-` pushed apart gives
   `y ∈ X`, and `supp y` splits into two parts at distance `> 2D`.
2. Hence (`sft-wall-rigidity-iff-idempotent-commutator-ideal`) the commutator ideal of every local tiling
   algebra of `X` is not idempotent. There are noncommuting two-dimensional families, and `LC(X, k) ⋊ Z^2`
   is not finitely presented over any field.

**Examples.** For `X_f = {c : sum_h f_h c(n + h) = 0}` with `f = 1 + x + y + xy` (a square Newton polygon),
the configurations `c(i, j) = a(i)` with `a` supported on `i > 0`, and on `i < 0`, are one-sided in the
directions `±e_1`.

**Reading.** In Bieri–Strebel's language this is the easy direction: an antipodal pair in `Σ^c` makes the
lamp group infinitely presented. The identification of `Σ^c` with one-sided directions is recalled, not
re-read.

Route: `antipodal-one-sided-group-shift-configurations-are-walls-proof`.
