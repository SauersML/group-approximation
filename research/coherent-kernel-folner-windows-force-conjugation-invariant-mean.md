---
rg: 2
id: coherent-kernel-folner-windows-force-conjugation-invariant-mean
kind: claim
title: Følner windows in a normal kernel chosen coherently along the ambient action force a translation- and conjugation-invariant mean on the kernel
invalidates: [amenable-kernel-ascent-via-coherent-kernel-windows]
distinct_from:
  free-presentation-kernel-has-no-conjugation-folner-exhaustion: that excludes conjugation Følner exhaustions of a free presentation kernel through inner amenability of free groups; this is about translation-Følner windows in a normal subgroup that are equivariant under the ambient group, and names the mean they produce.
  kun-thom-wreath-actor-subgroups-are-not-co-amenable: that proves non-co-amenability of actor-containing subgroups in lamp wreaths; this shows every coherent window scheme along a normal kernel yields a mean of that kind, so that theorem is the instance that kills the scheme on the Kun–Thom wreath.
  rokhlin-maximality-ascends-co-amenable-subgroups: that is the Rokhlin ascent along a co-amenable subgroup; this shows that window-based joint counting along a normal kernel needs the same kind of mean, which for split extensions is co-amenability of the complement.
---

Let `N ◁ W` be countable groups and `Q = W/N`.

**(CIM)** `N` carries a mean `m` with `m(kA) = m(A) = m(wAw^-1)` for all `k ∈ N`, `w ∈ W`, `A ⊆ N`.

**Coherent windows.** Let `W ↷ (Y, ν)` be a p.m.p. action. A *coherent window* is a measurable map
`y ↦ T_y` from `Y` to the finite nonempty subsets of `N` with `T_(wy) = w T_y w^-1` for every `w ∈ W`
and a.e. `y`. A sequence of coherent windows `T^(i)` on actions `(Y_i, ν_i)` is *asymptotically Følner*
if for every finite `K ⊆ N` and `δ > 0`,
`ν_i{ y : |k T^(i)_y Δ T^(i)_y| <= δ |T^(i)_y| for all k ∈ K } -> 1`.

Example: in a `W`-equivariant measurable tiling of the orbits of a free `N`-action, the tile containing
`y`, read as `T_y = { n : ny lies in the tile of y }`, is a coherent window. These are the Ornstein–Weiss
quasi-tilings along `N` that a joint count would use.

**Theorem.**
1. If an asymptotically Følner sequence of coherent windows exists, then (CIM) holds.
2. (CIM) holds exactly when the diagonal `Δ = {(w, w)}` is co-amenable in the fibre square
   `W ×_Q W = { (a, b) ∈ W × W : aN = bN }`.
3. If `W = N ⋊ Q` splits, (CIM) holds exactly when `Q` is co-amenable in `W`.
4. (CIM) holds when `N` is finite, when `N` is central and amenable, and when `W` is amenable. It fails
   for the Kun–Thom wreath `(Z/2) wr_(G/Γ) G` with the lamps as kernel.

**Consequence for `rokhlin-maximality-ascends-amenable-normal-extensions`.** A joint count that
transports Følner windows of `N` coherently along `W` consumes (CIM). This covers quasi-tilings of
`N`-orbits in any auxiliary `W`-system, windows read off a factor of the Bernoulli shift, and, through
item 3, the coset windows of Theorem A of `rokhlin-maximality-ascends-co-amenable-subgroups` for a
complement.
- For split extensions, (CIM) is co-amenability of the complement, and Theorem A already gives the ascent.
- On the Kun–Thom wreath (CIM) fails, so no such count reaches `kun-thom-wreath-bernoulli-rokhlin-maximal`.
- Window counts are left with the non-split extensions satisfying (CIM), for example finite and central
  kernels. Even there, the windows exist trivially (item 4), and what is missing is the `Q`-system to
  which maximality of `Q` would apply.

**ESTABLISHED 2026-09-13** by [[coherent-kernel-folner-windows-conjugation-mean-proof]]. Unreviewed.
