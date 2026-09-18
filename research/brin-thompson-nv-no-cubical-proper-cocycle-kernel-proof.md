---
rg: 2
id: brin-thompson-nv-no-cubical-proper-cocycle-kernel-proof
kind: route
title: "Conjugate one depth-2 swap by powers of the elliptic fibre element id × x_0: the kernel depth grows by one per power while the length and the cnd value stay controlled"
target: brin-thompson-nv-no-cubical-action-proper-on-cocycle-kernel
requires:
  - brin-thompson-nv-fibre-elements-are-cubically-elliptic
  - nv-cnd-functions-grow-at-most-linearly-along-fibre-elements
---

Notation is as in the target. Points of `C^n` are written `(x, w, v)` with `x, w ∈ C`,
`v ∈ C^{n−2}`. A *level-m cube* is `[u_1]×...×[u_n]` with all `|u_i| = m`.

**Step 1 (the conjugates).** By definition of `x_0`, `x_0[0] = [00]` and `x_0(0y) = 00y`, so
`x_0^M(0^j y) = 0^{M+j} y` for `j ≥ 1`, and `x_0^M [00] = [0^{M+2}]` as sets. The element `z`
moves only the second coordinate and `τ` moves only the first. Take `(x, w, v)`.
- If `w ∉ [0^{M+2}]`, then `x_0^{−M} w ∉ [00]`, so `τ` fixes `z^{−M}(x, w, v)` and `τ_M` fixes `(x, w, v)`.
- If `w ∈ [0^{M+2}]`, then `z^{−M}(x, w, v) = (x, x_0^{−M} w, v)` with `x_0^{−M} w ∈ [00]`. `τ`
  replaces the prefix `00` of `x` by `01` or conversely, and fixes the point if `x ∉ [00] ∪ [01]`.
  Then `z^M` returns the second coordinate to `w`.

So `τ_M` is the swap of `[00]×[0^{M+2}]×C^{n−2}` and `[01]×[0^{M+2}]×C^{n−2}` by prefix
replacement `00 ↔ 01` in the first coordinate, and the identity elsewhere. That set is a union of
level-`(M+2)` cubes, each moved by a prefix replacement of equal length, so `τ_M ∈ K_{M+2} ⊆ K`.
The supports differ for distinct `M`, so the `τ_M` are pairwise distinct.

*Depth is exactly `M + 2`.* Let `m ≤ M + 1`. Take `p = (000^ω, 0^{M+2}1^ω, 0^ω)`, which is moved
(its first coordinate becomes `010^ω`), and `q = (000^ω, 0^{M+1}1^ω, 0^ω)`, which is fixed. They lie
in one level-`m` cube `Q`. An element of `K_m` maps `Q` onto a level-`m` cube by prefix replacement,
and it fixes `q ∈ Q`, so it maps `Q` to itself by the identity replacement, and fixes `p`. So
`τ_M ∉ K_m`.

**Step 2 (class-kill).** Fix a commensurating action of `nV` with commensurated set `A`, and
`ℓ(g) = |gA Δ A|`. As in step 0 of `brin-thompson-nv-fibre-elements-are-cubically-elliptic-proof`,
`ℓ(ab) ≤ ℓ(a) + ℓ(b)` and `ℓ(a^{−1}) = ℓ(a)`. The element `z = id × x_0 × id^{n−2}` lies in
`V^n` (coordinatewise action), so by item 2 of `brin-thompson-nv-fibre-elements-are-cubically-elliptic`
it is elliptic: `L = sup_M ℓ(z^M) < ∞`. Hence `ℓ(τ_M) ≤ 2L + ℓ(τ)` for all `M`. By step 1,
`{τ_M}` is an infinite subset of `K` with bounded `ℓ`, so `{k ∈ K : ℓ(k) ≤ 2L + ℓ(τ)}` is infinite
and `ℓ|_K` is not proper. Actions on CAT(0) cube complexes and wall spaces are commensurating
actions with `ℓ(g) = d(v, gv)` for a vertex `v`, so they are included.

**Step 3 (forced shape).** Let `ψ` be cnd on `nV`. Write `ψ(g) = ‖β(g)‖²` for a cocycle `β` of an
affine isometric action (Schoenberg, with the usual normalization `ψ(1) = 0`; a constant shift changes none of the
conclusions). Then `√ψ` is subadditive and
symmetric, so `√ψ(τ_M) ≤ 2√ψ(z^M) + √ψ(τ)`. The element `z` acts as the identity on the first
coordinate and as `x_0 × id^{n−2} ∈ (n−1)V` on the others, so item 3 of
`nv-cnd-functions-grow-at-most-linearly-along-fibre-elements` gives `ψ(z^M) ≤ A + BM`. Hence
`ψ(τ_M) ≤ (2√(A + BM) + √ψ(τ))² = O(M)`. By step 1 the kernel depth of `τ_M` is `M + 2`.

**Step 4 (P3 forces `ψ(z^M) → ∞` and `ψ(b^M) → ∞`).** Let `ψ|_K` be proper. If
`ψ(z^{M_j}) ≤ R` along an infinite sequence `M_j`, then by step 3's inequality `ψ(τ_{M_j})` is
bounded, and the `τ_{M_j}` are pairwise distinct elements of `K`, contradicting properness. So
`ψ(z^M) → ∞`.

For the baker's map `b(x, y_1 r, v) = (y_1 x, r, v)` one has `b^{−M}(x, w, v) = (σ^M x, x_M ⋯ x_1 w, v)`
with `σ` the shift. Let `M ≥ 2` and `ρ_M = b^M τ b^{−M}`. The point `b^{−M}(x, w, v)` is moved by `τ`
iff `σ^M x ∈ [0]` and `x_M ⋯ x_1 w ∈ [00]`, i.e. iff `x_{M−1} = x_M = x_{M+1} = 0`, and then `τ`
flips the second letter `x_{M+2}` of `σ^M x`; `b^M` restores the prefix `x_1 ⋯ x_M` and `w`. So `ρ_M`
flips `x_{M+2}` on `{x_{M−1} = x_M = x_{M+1} = 0}` and is the identity elsewhere. This is a prefix
replacement of equal length on level-`(M+2)` cubes, so `ρ_M ∈ K`, and the supports are pairwise
distinct sets, so the `ρ_M` are pairwise distinct. The argument of the previous paragraph, with
`√ψ(ρ_M) ≤ 2√ψ(b^M) + √ψ(τ)`, gives `ψ(b^M) → ∞`. ∎
