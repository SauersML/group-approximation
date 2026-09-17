---
rg: 2
id: brin-thompson-nv-exponent-cocycle-pattern-depth-is-cnd-dominated
kind: claim
title: "For n >= 2 some cnd function on nV tends to infinity with the pattern depth of the exponent cocycle"
distinct_from:
  brin-thompson-nv-exponent-cocycle-scale-is-cnd-dominated: that asks growth with the magnitude ‖c(g)‖; this asks growth with the least level on whose cubes c(g) is constant, which can be unbounded while the magnitude stays 1 (conjugate x_0 into a deep cube)
  brothier-problem-b-reduces-to-value-range-domination: there the positional half of properness on C(C,Γ) ⋊ V came free from congruence quotients into V; this is the nV analogue, and nV has no such quotients
---

Let `n ≥ 2`, let `c: nV → C(C^n, Z^n)` be the exponent cocycle, and let `pd(g)` be the least `m`
such that `c(g)` is constant on every level-`m` cube (notation of
`brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination`).
The claim: there are a cnd function `ψ` on `nV` and `F: N → R` with `F(t) → ∞` such that
`ψ(g) ≥ F(pd(g))` for all `g ∈ nV`.

## Status

OPEN. It is prerequisite P2 of `brin-thompson-nv-a-t-menable-via-cocycle-and-kernel-domination`, and
it is necessary for `brin-thompson-groups-nv-are-a-t-menable`.

## Known

- It holds for `n` if it holds for some `m ≥ n`.
- No commensurating action witnesses it: `z = id × x_0` is elliptic in all of them, while
  `pd(z^M) ≥ M + 1`. So `ψ` must be non-cubical.
- Scale does not bound pattern depth. Let `w_m ∈ V` be `x_0` inside `[0^m]`
  (`0^m y ↦ 0^m x_0(y)`, identity elsewhere). Then `c(w_m)` is `1` on `[0^{m+1}]`, `0` on
  `[0^m 10]`, `−1` on `[0^m 11]` and `0` off `[0^m]`, so `‖c(w_m)‖ = 1` and `pd(w_m) = m + 2`.
  Also `id × w_m ∈ 2V` is elliptic in every commensurating action. In the other direction
  `pd'(gh) ≤ max(pd'(h), pd'(g) + ‖c(h)‖)`, so P1 and P2 interact only through products.
- The Kazhdan host `(M ⋊ Γ) × G_2` does not obstruct a cocycle-only proof, since `Γ` has
  cocycle `0`.

## Attempts

- **Wall counts (2026-09-17, swarm-0917-w5-nv-decomp; dies).** Any commensurating action: `id × w_m` and
  `id × x_0^M` are elliptic, while `pd` grows linearly in `m` and `M`. The next step is the computation of
  `pd(f^N)` versus `‖c(f^N)‖` for the Callard–Salo element, from its conveyor construction (deferred).
