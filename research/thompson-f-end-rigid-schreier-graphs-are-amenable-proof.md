---
rg: 2
id: thompson-f-end-rigid-schreier-graphs-are-amenable-proof
kind: route
title: Long x_0-rays toward an end of the interval are almost invariant in end-rigid Schreier graphs of F
target: thompson-f-end-rigid-schreier-graphs-are-amenable
requires: []
artifacts:
  - research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13.md
---

Full proof: `research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13.md`, §1,
Theorem A. Outline, in the case `F_[c,1] ⊆ Stab_F(y)` (the other case follows by conjugating
with `t ↦ 1 - t`, which normalizes `F`):

1. Each `s ∈ S` fixes `0` with finitely many breakpoints, so `s(t) = 2^(k_s) t` on some
   `[0, ε_s]`. Put `K = max |k_s|`.
2. `x_0` halves on `[0,1/2]` and `x_0^j(c) → 0`. Choose `N ≥ K` with
   `x_0^(N-K)(c) ≤ 2^(-K) min ε_s`. For `n ≥ N` and `t ∈ [0,c]`, both
   `s(x_0^n t) = 2^(k_s) x_0^n t` and `x_0^(n-k_s)(t) = 2^(k_s) x_0^n(t)` hold, since all
   intermediate points lie in `[0,1/2]`. So `r_(s,n) = x_0^(-(n-k_s)) s x_0^n` is the identity
   on `[0,c]` and fixes `y`.
3. Hence `s·(x_0^n y) = x_0^(n-k_s) y` for `n ≥ N`. If the points `x_0^n y` are distinct, the
   window `{x_0^n y : N+K ≤ n < N+K+M}` has `M` points and at most `sum |k_s|` boundary pairs.
   If `x_0^p y = y` for some `p ≥ 1`, the finite set `{x_0^n y}` is `S`-invariant, hence the
   whole orbit.

Instances: `Stab_F(t) ⊇ F_[c,1]` for `c ≥ t`, and a finite set `E ⊂ (0,1)` is fixed by
`F_[c,1]` once `c ≥ max E`.
