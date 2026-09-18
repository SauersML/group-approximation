---
rg: 2
id: brin-thompson-nv-no-cubical-action-proper-on-cocycle-kernel
kind: claim
title: "For n >= 2 no commensurating action of nV is proper on the cocycle kernel K, and every cnd function grows at most linearly in kernel depth along an explicit deep family; so P3 is forced non-cubical"
distinct_from:
  brin-thompson-nv-fibre-elements-are-cubically-elliptic: that makes infinite-order fibre elements elliptic, which kills cubical properness on subgroups containing them; K is torsion, so nothing there applies to it directly. This conjugates a fixed kernel element by powers of an elliptic fibre element to get an infinite, bounded-length subset of K
  nv-cnd-functions-grow-at-most-linearly-along-fibre-elements: that bounds cnd growth along powers of fibre elements; this transfers the bound into K, along conjugates of unbounded kernel depth
  brin-thompson-nv-no-cubical-action-proper-mod-triangular: that forces the transversal half of the triangular split non-cubical; this forces the kernel prerequisite P3 of the cocycle-and-kernel split non-cubical
  brin-thompson-nv-cnd-proper-on-cocycle-kernel: that is the positive claim P3, which stays OPEN; this is a class-kill of one proof strategy for it and a constraint on the shape of every witness
---

**ESTABLISHED** by `brin-thompson-nv-no-cubical-proper-cocycle-kernel-proof`.

**Setting.** Notation of `brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination`: `nV` acts on
`C^n`, `c` is the exponent cocycle, `K = ker c = ⋃_m K_m`, and the kernel depth of `k ∈ K` is the
least `m` with `k ∈ K_m`. Let `x_0 ∈ V` be `0y ↦ 00y`, `10y ↦ 01y`, `11y ↦ 1y`. Let
`z = id × x_0 × id^{n−2}`. Let `τ ∈ K_2` swap `[00]×[00]×C^{n−2}` and `[01]×[00]×C^{n−2}` by
prefix replacement in the first coordinate, and fix everything else. Put `τ_M = z^M τ z^{−M}`.

**Statement.** Let `n ≥ 2`.

1. `τ_M` swaps `[00]×[0^{M+2}]×C^{n−2}` and `[01]×[0^{M+2}]×C^{n−2}` by prefix replacement
   in the first coordinate. So `τ_M ∈ K`, the `τ_M` are pairwise distinct, and the kernel depth
   of `τ_M` is exactly `M + 2`.
2. **(Class-kill.)** In every commensurating action of `nV`, `sup_M ℓ(τ_M) < ∞`. So no
   commensurating action (in particular no action on a CAT(0) cube complex or a wall space) has
   `ℓ` proper on `K`.
3. **(Forced shape.)** For every cnd function `ψ` on `nV`, `ψ(τ_M) = O(M)`. So every witness
   `ψ_3` of P3 grows at most linearly in kernel depth along `{τ_M}`.
4. **(P3 forces non-ellipticity of z.)** If `ψ` is cnd and `ψ|_K` is proper, then
   `ψ(z^M) → ∞`. The same holds for the baker's map `b(x, y_1 r, w) = (y_1 x, r, w)`:
   `ψ(b^M) → ∞`.

**Consequence for the goal.** With supplement (d) of
`brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination` (P1 and P2 are non-cubical), all
three prerequisites of `brin-thompson-nv-a-t-menable-via-cocycle-and-kernel-domination` are now
forced to be non-cubical. This corrects the remark recorded in that route and in
`brin-thompson-nv-cnd-proper-on-cocycle-kernel` that "no known elliptic family inside `K` has
unbounded kernel depth": `{τ_M}` is one.

**Invariant and death step.** The invariant is *the length ℓ of an elliptic conjugator*. Every
commensurating candidate dies at the family `z^M τ z^{−M}`: the conjugator `z^M` has bounded
length (ellipticity of fibre elements), so the conjugates have length at most `2 sup ℓ(z^M) + ℓ(τ)`,
while their kernel depth is `M + 2`.

**Not claimed.** Anything about non-commensurating cnd functions beyond item 3; a lower bound on
`ψ_3(τ_M)`; ellipticity of the baker's map (item 4 only says a P3 witness is unbounded on it).
