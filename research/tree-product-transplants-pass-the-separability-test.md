---
rg: 2
id: tree-product-transplants-pass-the-separability-test
kind: claim
title: In a Busemann transplant over F_m x F_n with the arrow skeleton, every skeleton modification contains a slab whose Busemann image is all of Z^2, so it meets every other modification; the transplant has separable modifications only if its fibre does, and the F_2 x F_2 transplant passes the test
requires:
  - cross-layer-separable-modifications-kill-quantum-rigidity
  - busemann-transplant-minimality-is-horospherical-minimality
distinct_from:
  busemann-transplant-minimality-is-horospherical-minimality: that proves minimality of the transplant from density of the zero-lag relation; this checks the classical necessary condition for rigidity, and its mechanism is the modification-set counterpart of that density.
  crossing-wire-shifts-pass-the-separability-test: that checks the Z^2 fibre; this checks the skeleton-fibre and cross-factor pairs that the transplant adds.
---

**ESTABLISHED** (lane bh-free-09, 2026-09-18; elementary lane proof, not independently reviewed; no
priority claimed).

## Setting

This is item 5 and the Corollary of `busemann-transplant-minimality-is-horospherical-minimality`.
- `Γ = F_m × F_n` (`m, n >= 2`) acts on trees `T_1 × T_2`.
- The skeleton is the arrow skeleton `∂T_1 × ∂T_2`: at each vertex, one pointer toward `ξ_1` and one
  toward `ξ_2`.
- `b = (b_1, b_2)` are the Busemann functions, normalized at the base vertex.
- The transplant of a `Z²`-subshift `Y` along `M` puts at `(g_1, g_2)` the skeleton letters and the tile
  `y(M^(-1) b(g_1, g_2))`.
- It is a skew product, so every pair (skeleton point, fibre point) is a point.

## Theorem

Let `x = (ξ, y)` be a point of the transplant.
1. **Skeleton modifications contain a surjective slab.** Let `x'` have `ξ'_1 ≠ ξ_1`. Then
   `Δ(x, x') ⊇ ℓ × T_2`, where `ℓ` is the geodesic line of `T_1` from `ξ'_1` to `ξ_1`, and
   `b(ℓ × T_2) = Z²`. The same holds for the second factor.
2. **Pure fibre modifications are pullbacks.** If `ξ' = ξ`, then `Δ(x, x') = b^(-1)(M Δ(y, y'))`, a union
   of full fibres of `b`.
3. **No separable pair involves the skeleton.** Any modification that changes the skeleton meets every
   other modification of the same point.
4. **Fibre pairs reduce to the fibre.** Distances between unions of `b`-fibres equal the `ℓ¹` distances
   of their images. So two pure fibre modifications are separable upstairs iff their `Z²`-difference
   sets are separable.

Hence the transplant has a separable pair of modifications only if `Y` does. For
`Y = Ω_min ∘ M^(-1)` (bh-invent-04's Corollary), the fibre passes by
`crossing-wire-shifts-pass-the-separability-test`. **So the `F_2 × F_2` transplant passes, and no
freedom is separable across the two tree factors.**

## Proof

- **Item 1.**
  - *Where the pointer changes.* The pointer at `g_1` is the first step of the ray from `g_1` to
    `ξ_1`. The rays to `ξ_1` and to `ξ'_1` start differently exactly when `g_1` lies on the line
    `ℓ = (ξ'_1, ξ_1)`. So the first pointer differs on all of `ℓ × T_2`, whatever happens to the
    tiles.
  - *The slab is surjective.* `b_1` restricted to `ℓ` takes every integer value, because it tends to
    `+∞` toward `ξ_1` and to `−∞` toward `ξ'_1` in steps of `1`. `b_2` restricted to `T_2` also takes
    every value.
- **Item 2.** The skeleton, and hence `b`, is unchanged. The tile at `γ` is `y` or `y'` read at
  `M^(-1) b(γ)`.
- **Item 3.** Let `x_1` change the skeleton, with slab `ℓ × T_2`. Let `x_2` be any other
  modification.
  - *`x_2` also changes `ξ_1`.* Both lines end at `ξ_1`, so they share a ray, and the slabs intersect.
  - *`x_2` changes only `ξ_2`.* Then `(ℓ × T_2) ∩ (T_1 × ℓ_2) = ℓ × ℓ_2 ≠ ∅`.
  - *`x_2` is a pure fibre modification with `Δ(y, y') ∋ z`.* By item 1 some vertex of `ℓ × T_2` lies
    over `Mz`, and by item 2 that vertex lies in `Δ(x, x_2)`.
- **Item 4.**
  - *`b` does not increase distances.* It is 1-Lipschitz for the `ℓ¹` metric.
  - *Every step lifts.* From any vertex, one neighbour raises `b_i` by `1` (toward `ξ_i`) and another
    lowers it by `1`. So a lattice path from `b(γ)` lifts to an edge path from `γ` of the same length.
  - *Conclusion.* The distance between `b^(-1)(A)` and `b^(-1)(B)` is the `ℓ¹` distance of `A` and
    `B`. `∎`

## Scope and what to check elsewhere

- **The mechanism.** Every skeleton modification is **Busemann-surjective**: its difference set
  contains vertices at every horospherical level. It therefore cannot avoid a fibre modification,
  which occupies whole levels. This is the modification-set form of bh-invent-04's horospherical
  condition (zero-lag orbits see everything).
- **For `Ã₂` lattices (not checked).** The analogous claim is that changing the chamber `c` to `c'`
  changes germs on a set whose `b_c`-image is all of `L`. If the germ-difference set of some chamber
  change had a Busemann image missing a half-plane, a fibre modification supported there could be
  separable. That is the one point to verify for `a2-busemann-transplants-preserve-quantum-rigidity`
  designs.

## Lesson for general BH

- **Skew products are fibre products twisted by a cocycle,** so they are exactly where separable
  freedom could hide. The twist protects them when every skeleton modification is Busemann-surjective.
- **Tree skeletons have this for free.** Changing an end flips pointers along a whole line, which
  crosses every horosphere.
- **Design rule for transplants and any cocycle-coupled layering.** The base's modification sets must
  map onto the fibre's group. Then the fibre is the only place where rigidity can fail, and the fibre
  is checked by its own tests.
