---
rg: 2
id: open-boundary-fixers-fix-balls-proof
kind: route
title: Branching apartments across walls of every direction force the translation part to vanish, sectors are then fixed by convexity, and a CAT(0) comparison puts balls inside shadow cones
target: automorphisms-fixing-open-boundary-sets-fix-large-balls
requires: [euclidean-building-lattices-lie-in-permutational-bh-class]
---

Notation: `Ch(∂X)` is the spherical building at infinity with the cone topology.
`S(x, C)` is the sector from `x` toward `C`. For a vertex `o` and a box `p` based at
`o`, the shadow `Ω_o(p)` is the set of `C` with `S(o, C) ⊇ p`. Shadows based at any
fixed special vertex form a basis of the cone topology.

**Step 1 (an apartment with a translation).** Pick `C_1 ∈ U`. The chambers opposite
`C_1` are dense (cited), so there is `C_2 ∈ U` opposite `C_1`. `A = A(C_1, C_2)` is the
unique apartment with both in its boundary, so `h A = A`. `h` fixes two opposite
chambers of the Coxeter complex `∂A`, so on `A` it acts as `x ↦ σx + v`, where `σ` is
linear and preserves the Weyl chamber of `C_1` (a diagram symmetry, if `h` permutes
types).

**Step 2 (σ = 1 and v = 0).** Let `β` be a root that is positive on the chamber of
`C_1`, choose `c ≪ 0`, and let `R = {β >= c} ⊆ A`.
- **Branching.** By thickness there is an apartment `A' = R ∪ R'` with `A ∩ A' = R`
  (standard).
- **The new chamber is in U.** `R` contains a subsector toward `C_1`, so `C_1 ∈ ∂A'`.
  Let `C_2'` be the chamber of `∂A'` opposite `C_1`. The isomorphism `A' -> A` fixing
  `R` sends `C_2'` to `C_2`. Fix a base vertex `o ∈ A` and a large box `p` in `S(o, C_2)`
  with `Ω_o(p) ⊆ U`. For `c` small enough, `o` and `p` lie in `R`, so `S(o, C_2')` also
  contains `p`, and `C_2' ∈ U`.
- **Preserving the root.** Hence `h` fixes `C_1` and `C_2'`, so `h A' = A'`, and `h`
  preserves `A ∩ A' = R`. From `h(R) = {(β∘σ^(-1)) >= c + β(σ^(-1)v)}` we get
  `β∘σ^(-1) = β` and `β(σ^(-1)v) = 0`.
The positive roots span the dual space, so `σ = 1` and `v = 0`: `h` fixes `A`
pointwise. The same argument works with any `C ∈ U` opposite `C_1` in place of `C_2`.
This is item 1. For a tree, roots are half-lines, and this is the branch-point
argument.

**Step 3 (fixed sectors).** `h` fixes `o ∈ A`. For `C ∈ U' = U ∩ opp(C_1)`, which is
open and nonempty, `h` fixes the apartment `A(C_1, C)` pointwise. That apartment
contains a subsector `S(x', C)` of `S(o, C)`, since parallel sectors share subsectors.
The fixed set of an isometry of a CAT(0) space is closed and convex. The convex hull of
`o` and `x' + cone` contains the interior of `o + cone`: write `o + y` as
`(1-t) o + t(x' + z)` with `z = y/t - (x' - o)`, which lies in the open cone for
small `t`. So `h` fixes `S(o, C)` pointwise.

**Step 4 (balls inside a shadow cone, item 2).** Choose a box `p` from `o` with
`Ω_o(p) ⊆ U'`, and let `q` be an interior point of its far chamber, at distance
`η > 0` from that chamber's boundary. Take `w` beyond `p` with `[o, w]` passing
through `q`, and `D = d(o, w) >= d(o, q) R / η`. Let `d(z, w) <= R`.
- **Comparison.** CAT(0) comparison for geodesics from `o`, parametrized
  proportionally, puts the point of `[o, z]` at parameter `d(o,q)/D` within
  `(d(o,q)/D) R <= η` of `q`, hence inside the open far chamber of `p`.
- **A sector through p.** `z` lies in some sector `S(o, C_z)`, which contains `[o, z]`
  by convexity, hence that far chamber. So its initial box of the shape of `p` is `p`
  (a box is the convex hull of `o` and its far chamber), and `C_z ∈ Ω_o(p) ⊆ U'`.
- **Conclusion.** By Step 3, `h` fixes `z`. So `h` fixes `B(w, R)` pointwise, and `R`
  was arbitrary.

**Consequence.** As stated in the target: a finite group has no infinite strictly
decreasing chain of subgroups, and finitely many orbits of vertices give one radius
for all vertices.
