---
rg: 2
id: brin-thompson-nv-exponent-cocycle-scale-is-cnd-dominated
kind: claim
title: "For n >= 2 some cnd function on nV tends to infinity with the sup-norm of the exponent cocycle"
distinct_from:
  cantor-integer-maps-sup-norm-is-cnd-dominated: that asks growth with ‖f‖_∞ on C(C,Z) ⋊ V; this asks growth with ‖c(g)‖ on all of nV, and for n = 2 it implies that claim (supplement (c) of brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination), but no converse is known
  brin-thompson-nv-cnd-proper-modulo-triangular-subgroup: that asks properness modulo T_n, which contains elements of unbounded scale; this asks only for growth in scale, ignoring pattern and kernel
---

Let `n ≥ 2`, and let `c: nV → C(C^n, Z^n)` be the exponent cocycle with `‖c(g)‖ = max_{x,i} |c(g)(x)_i|`.
The claim: there are a cnd function `ψ` on `nV` and `F: N → R` with `F(t) → ∞` such that
`ψ(g) ≥ F(‖c(g)‖)` for all `g ∈ nV`.

## Status

OPEN. It is prerequisite P1 of `brin-thompson-nv-a-t-menable-via-cocycle-and-kernel-domination`, and
it is necessary for `brin-thompson-groups-nv-are-a-t-menable`.

## Known

- For `n = 2` it implies `cantor-integer-maps-sup-norm-is-cnd-dominated`, hence
  `cantor-integer-maps-by-v-have-haagerup-property`.
- It holds for `n` if it holds for some `m ≥ n`.
- No commensurating action (wall count) witnesses it: `id × x_0` is elliptic in all of them while
  `‖c((id × x_0)^M)‖ ≥ M`. So `ψ` must be non-cubical.
- The Kazhdan host `(M ⋊ Γ) × G_2` does not obstruct a groupoid-generic proof, since `Γ` has
  cocycle `0`.
- `‖c‖` is a sup, not an average. Integrated walls with subexponential germ-size weights
  (dead lane `e-nv-walls`) can only see the scale on sets of positive measure, while `M·1_U` in
  `C(C,Z) ⋊ V` has scale `M` on a set `U` of arbitrarily small measure.

## Attempts

- **Wall counts (2026-09-17, swarm-0917-w5-nv-decomp; dies).** Any commensurating action: `id × x_0`
  is elliptic (`brin-thompson-nv-fibre-elements-are-cubically-elliptic`) while `‖c((id × x_0)^M)‖ = M`.
  Deferred: the route schedules P1 last. Try P2 and P3 first.
