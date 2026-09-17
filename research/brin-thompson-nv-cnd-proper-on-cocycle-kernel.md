---
rg: 2
id: brin-thompson-nv-cnd-proper-on-cocycle-kernel
kind: claim
title: "For n >= 2 some cnd function on nV is proper on the locally finite kernel of the exponent cocycle"
distinct_from:
  brin-thompson-nv-cnd-proper-on-triangular-subgroup: that asks properness on T_n, which contains infinite-order undistorted elements; this asks properness only on K = ker c, a directed union of finite symmetric groups, where every element is torsion
---

Let `n ≥ 2`, let `c` be the exponent cocycle of `nV`, and let `K = ker c = ⋃_m K_m` with
`K_m ≅ Sym(2^{nm})` the prefix-replacement permutations of level-`m` cubes (notation of
`brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination`).
The claim: there is a cnd function `ψ` on `nV` whose restriction to `K` is proper, i.e.
`{k ∈ K : ψ(k) ≤ R}` is finite for every `R`.

## Status

OPEN. It is prerequisite P3 of `brin-thompson-nv-a-t-menable-via-cocycle-and-kernel-domination`, and
it is necessary for `brin-thompson-groups-nv-are-a-t-menable`.

## Known

- It holds for `n` if it holds for some `m ≥ n`.
- `K` alone is locally finite, hence Haagerup. The claim is about a cnd function defined on all of
  `nV`, so it is a statement about how `nV` weighs the finite pieces.
- The torsion-free kills do not reach it: no recorded elliptic family has unbounded kernel depth.
- A groupoid-generic proof must use that `K` is locally finite. In the Kazhdan host
  `(M ⋊ Γ) × G_2` the kernel of the `Z`-cocycle contains `Γ`.
- **Test family.** Let `τ_m ∈ K_m` swap two sibling level-`m` cubes. For `m ≥ 2` the support of
  `τ_m` is a proper clopen set, so `τ_m` is conjugate to `τ_2` in `nV`. A conjugator `g` maps
  `supp τ_2` (measure `2^{1−2n}`) onto `supp τ_m` (measure `2^{1−nm}`), so `Σ_i c(g)(x)_i ≥ n(m−2)`
  at some `x`, and `‖c(g)‖ ≥ m − 2`. So P3 asks `ψ(g τ_2 g^{-1}) → ∞` along conjugators whose
  scale is forced to grow, and P1 is consistent with that.

## Attempts

- **Deferred (2026-09-17, swarm-0917-w5-nv-decomp).** The obvious attack is to extend a proper cnd
  function on the locally finite `K` (for example the kernel depth itself) to `nV`, and it fails
  because the kernel depth is not conjugation-invariant up to bounded error: `g τ_2 g^{-1} = τ_m`. So an
  extension must pay for conjugators of scale `≥ m − 2`. That is the next thing to test: a cnd function
  on `nV` that is unbounded on `{τ_m}`.
