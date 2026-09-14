---
rg: 2
id: recurrent-orbit-closure-with-unique-sturmian-minimal-set
kind: claim
title: There is a subshift that is the orbit closure of a recurrent, not uniformly recurrent point whose only minimal subset is a Sturmian subshift, so EL_n over it has the subsystem dictionary although its limit sets are not separated
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
---

**ESTABLISHED (unreviewed)** via `recurrent-orbit-closure-unique-minimal-set-proof`.

Construction: fix irrational α, y ∈ X_α, and integers n_1 < n_2 < … with N_k = n_1 + … + n_k such that:
- n_{k+1} ≥ 3N_k + k;
- y[−N_k,N_k] = y[n_{k+1}−N_k, n_{k+1}+N_k].

Put P = {finite subsums of the n_i}, x_t = (y_t, 1_P(t)) and X = cl O(x). Then:
- x is recurrent and not uniformly recurrent;
- the only minimal subset of X is Y = X_α × {0^∞};
- ω(x) = X meets Y, so the limit-set hypothesis of `subshift-restriction-kernel-is-relative-elementary` fails.

For n ≥ 3 the normal subgroups of EL_n(LC(X,F_2)⋊Z) correspond exactly to the closed invariant subsets of X. The kernel onto Y is locally finite, with quotient EL_n(LC(X_α,F_2)⋊Z), an infinite simple Kazhdan LEF group.
