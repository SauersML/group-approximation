---
rg: 2
id: recognizable-morphisms-collapse-quantum-rigidity-to-one-scale
kind: claim
title: A Z^2 SFT with a locally recognizable shape-consistent self-morphism whose letter images have sides at least 2 is quantum rigid iff it is rigid at the single scale max(r, 1, ceil(R/2)); non-commuting operator tilings double in scale
requires:
  - sft-crossed-product-fp-iff-quantum-rigid
  - morphism-towers-double-covariant-tiling-scales
distinct_from:
  self-similar-sfts-are-quantum-rigid-iff-rigid-at-one-scale: that needs one constant block shape, so the block grid is fixed and non-commutation pulls back by summing over positions; this allows letter-dependent shapes (Labbé), where the grid is an operator-valued tower pointer, and uses recognizability to put the pointer's corner projection into the child algebra.
  morphism-towers-double-covariant-tiling-scales: that inflates finite-dimensional covariant families and only needs a nonzero result (existence of modules); this proves that the inflated family commutes only if the parent does, in any dimension, so NON-commutation doubles in scale.
  sft-wall-rigidity-iff-idempotent-commutator-ideal: that characterizes the first-order part of rigidity at a fixed scale; this shows the scale is immaterial, so J_D vanishes for all D >= D_* or for none.
artifacts:
  - research/artifacts/gq-bh-g2-labbe-morphic-scale-collapse.md
---

**ESTABLISHED (2026-09-18)** through `recognizable-morphism-scale-collapse-proof`. This is a lane proof by
bh-g2-labbe: elementary and unreviewed. No priority is claimed. A search of the quantum-rigidity nodes on main found
only the constant-shape case.

## Setting

- **The shift.** `Ω ⊆ A^(Z^2)` is an SFT with forbidden patterns in the sup-norm ball `B_r`.
- **The morphism.** `ω` is a 2-dimensional morphism on `L(Ω)` in Labbé's sense. It satisfies:
  - (H1) `ω(L(Ω)) ⊆ L(Ω)`;
  - (H2) every letter image has width and height `>= 2`;
  - (H3) **local recognizability at radius `R`.** A map on legal `B_R`-windows reads off, from `ω(x)|_(p + B_R)`,
    whether `p` is the lower-left corner of a block of the layout of `ω(x)`, and if so, the parent letter.
- **Families and rigidity** are as in `sft-crossed-product-fp-iff-quantum-rigid`, with the sup norm. They may have any
  dimension and need not be translation covariant.

## Statement

Put `D_* = max(r, 1, ⌈R/2⌉)`.
1. **Doubling of non-commutation.** For `D >= D_*`, every non-commuting `D`-family over a field `k` yields a
   non-commuting translation-covariant `2D`-family over `k`.
2. **Scale collapse.** `Ω` is quantum rigid iff it is `D_*`-rigid, iff it is `D`-rigid for every `D >= D_*`. Over
   every field, `LC(Ω, k) ⋊ Z^2` is finitely presented iff its scale-`D_*` local presentation already presents it.
   Equivalently, the idempotent commutator ideal `J_(D_*)` vanishes.
3. **Walls.** The same doubling applied to upper-triangular families shows the following. If `Ω` is `D_0`-wall-rigid
   for some `D_0`, then it is `D`-wall-rigid for every `D >= D_*`
   (`sft-wall-rigidity-iff-idempotent-commutator-ideal`, item 4).
4. **Two shifts.** Let `ω` go from `Ω_S` to `Ω_T`, with (H1) in the form `ω(L(Ω_S)) ⊆ L(Ω_T)`, (H2), and (H3) on
   layouts `ω(x)`, `x ∈ Ω_S`. Then non-commuting `Ω_S`-families at scale `D >= max(r_S, 1, ⌈R/2⌉)` give non-commuting
   `Ω_T`-families at scale `2D`. In particular, if `Ω_T` is quantum rigid, so is `Ω_S`.

## Mechanism

1. **Covariantize.** Take the direct sum of all translates of the family.
2. **Inflate.** Build the covariant tower of `morphism-towers-double-covariant-tiling-scales`, extended to any
   dimension.
3. **Evaluate two-sidedly.** On the ball `B_R`, the child idempotents are diagonal, with entries that are evaluations
   of classical letter functions on the parent ball `B_(⌈R/2⌉)`.
4. **Recognize.** By (H3), a sum of child ball-products equals the parent idempotent `E'_a(0)` on the corner summand
   and vanishes elsewhere. So the corner projection `Q_00`, the width projections `μ_m`, and the parent's own tiles
   lie in the child algebra.
5. **Descend.** The compressions `Q_00 A_1^(∓m) μ_m Q_00` equal `u_1^(−1) M_(=m)(0)` and `M_(=m)(0) u_1`.
   - If the child algebra is commutative, its corner is commutative and contains `M_(=m)(−e_1)`.
   - `Σ_m` of these compressions then conjugates the corner by the parent translations.
   - So the corner contains every parent idempotent `E'_a(Z)`, and they all commute.

## Instance

`labbe-shift-is-quantum-rigid-iff-rigid-at-scale-two`: `ω²` on Labbé's `Ω_U` has `r = 1` and `R = 3` (exact), so
`D_* = 2`.

## Lesson for general BH

For the master route's gate E2 (quantum rigidity), **scale is not a resource** for any self-similar SFT whose
self-similarity is recognizable, constant shape or not. This covers essentially every hierarchical aperiodic SFT used
to build minimal free shifts.
- `J_D` vanishes for all `D >= D_*` or for none.
- A single non-commuting operator tiling at scale `D_*` kills the candidate everywhere. By
  `zd-derived-full-group-fp-forces-quantum-rigidity` it also kills finite presentation of its derived full group
  (`char k ∉ {3,5}`).
- A proof of rigidity must work at the fixed commutation radius `2D_*`, or equivalently at any convenient larger
  radius.
- **Level induction.** A "level induction" in which rigidity of level-`n` supertiles feeds level `n+1` cannot close
  on scale alone. Its induction parameter must be commutation distance at a fixed scale. That is the parameter the
  determinism closure uses, and fault slabs block it in their normal directions
  (`determinism-closure-certifies-quantum-rigidity`).
- **Where E2 lives.** For substitutive candidates, E2 becomes a question about one explicit finitely presented algebra
  (the scale-`D_*` presentation). Item 4 says that recognizable morphisms push rigidity **down** chains of shifts. So a
  rigid "top" shift certifies every shift that maps into it, which gives a way to transport a single rigidity
  certificate across a family of hierarchical tilings.
