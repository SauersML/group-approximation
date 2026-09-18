---
rg: 2
id: rigid-subshifts-without-isolated-points-factor-onto-the-ends
kind: claim
title: Over any finitely generated group, a quantum-rigid subshift without isolated points factors continuously and equivariantly onto the space of ends; so (RA) holds for every virtually free group, and over multi-ended groups non-amenable isotropy lives only over ends of one-ended vertex groups
requires:
  - rigid-subshifts-over-free-factors-are-tight-almost-everywhere
distinct_from:
  rigid-subshifts-over-free-factors-are-tight-almost-everywhere: that works over Λ_0 × F_n with slabs, and proves (RA) over F_n; this uses balls in an arbitrary finitely generated group, where the free branches converge to a Freudenthal end.
  quantum-rigid-minimal-topfree-subshift-actions-are-amenable: that is the open question (RA); this settles it for virtually free groups and reduces it, for multi-ended groups, to one-ended pieces.
---

**ESTABLISHED** (lane proof, elementary; bh-star-b, 2026-09-18; not reviewed; no priority claimed).
Items 3 and 4 use standard facts, recalled and not re-read.

## Setting

- `Λ` is finitely generated, with a word metric and balls `B_r`.
- `X ⊆ A^Λ` is a subshift (finite type not assumed), `D`-quantum rigid over some field, with no
  isolated points.
- Fix `w >= 2D`. The *`r`-cylinder* of `x` is the set of points agreeing with `x` on `B_(r+w)`.
- `Ends(Λ)` is the Freudenthal end space: compatible choices of an infinite component of `Λ \ B_r`,
  one for each `r`.

## Theorem

1. **One deep component.** Let `C_1, C_2, …` be the components of `Λ \ B_r`, with deep parts
   `C_i^w = {g ∈ C_i : d(g, B_r) > w}`. Every `r`-cylinder has an index `i` such that its points agree
   off `C_i^w`.
2. **The end map.** For `x ∈ X` these components are infinite and nested as `r` grows. They define an
   end `ξ(x)`, and `ξ : X → Ends(Λ)` is continuous and `Λ`-equivariant. In particular
   `Stab(x) ⊆ Stab(ξ(x))`.
3. **Virtually free groups.** If `Λ` is virtually free, then `Λ ↷ X` is topologically amenable. This is
   (RA) for such `Λ`, with no minimality or freeness hypothesis beyond the absence of isolated points.
4. **Multi-ended groups.**
   - Let `Λ` be finitely presented and multi-ended, so accessible (Dunwoody). Its ends split into ends
     of the Bass–Serre tree of a splitting over finite groups, and ends of the one-ended vertex groups.
   - A point `x` with `ξ(x)` a tree end has amenable isotropy, since end stabilizers are
     locally-finite-by-cyclic.
   - So any non-amenable isotropy of a rigid `X` sits over the ends of one-ended vertex groups. The
     non-amenability of a rigid action over a multi-ended group can only come from its one-ended
     pieces.

## Proof

1. **One deep component.** Suppose `y, y'` in one cylinder differ in two deep parts `C_i^w` and
   `C_j^w`. Let `z` be `y'` on both deep parts, and `y` elsewhere.
   - A point of `C_i^w` is at distance `> w >= 2D` from `B_r`, and every path leaving `C_i` meets
     `B_r`. So a `D`-ball meeting `C_i^w` lies in `C_i`, where `z = y'`, because `y = y'` on
     `B_(r+w) ⊇ C_i \ C_i^w`.
   - Every other ball reads `y`. So `z` is locally legal, and `Δ(y, z)` is two nonempty pieces at
     distance `> 2D`.
   - Lemma 1′ of `rigid-subshifts-over-free-factors-are-tight-almost-everywhere` then refutes
     rigidity. Differences in two different single parts reduce to this case.
2. **The end map.**
   - *Nesting.* The `(r+1)`-cylinder lies in the `r`-cylinder. Every component of `Λ \ B_(r+1)` lies
     in a component of `Λ \ B_r`.
   - *Infinite components.* Since `x` is not isolated, every cylinder has at least two points. If the
     component at level `r` were finite, it would lie in `B_(r')` for some `r'`. The `r'`-cylinder
     would then vary nowhere, so it would be `{x}` and `x` would be isolated, a contradiction.
   - *Continuity.* The component at level `r` is a function of the `r`-cylinder, which is open. So `ξ`
     is continuous.
   - *Equivariance.* Cylinders about `c` are sandwiched between cylinders about `1`, as in the
     free-factor node. So the end does not depend on the centre, and `ξ(g.x) = g ξ(x)`.
3. `Λ` virtually free means `Λ` acts properly and cocompactly on a locally finite tree, and `Ends(Λ)`
   is its boundary. The boundary action of a hyperbolic group is topologically amenable (recalled). A
   continuous equivariant map to an amenable action pulls back approximately invariant maps. For
   two-ended `Λ`, the group is amenable. For finite `Λ` the statement is empty.
4. *End stabilizers.* An element fixing a tree end either fixes a subray, and so lies in an increasing
   union of finite edge groups, or translates along an axis ending there. So the stabilizer is
   (locally finite)-by-(Z or 1), which is amenable. Then use `Stab(x) ⊆ Stab(ξ(x))`. ∎

## Calibration

- **End shift of `F_n`.** `ξ` is the coded end.
- **Stabilizer engines `X_B`.** They are not rigid (`v-stabilized-stabilizer-engines-are-never-finitely-presented`).
  Consistently with item 4, their vertex points would sit over the one-ended vertex group's end with
  isotropy `B`.
- **Two-ended and one-ended groups.** `Ends(Λ)` has at most two points and the theorem says nothing,
  as it must: Ã₂ lattices (one-ended, rigid) and the Cornulier regime over `V` (one-ended) are
  consistent with it.

## Lesson for general BH

**Splittings over finite groups are boundaries for free.**
- Rigidity turns every finite cut of the group into a choice of side.
- The choices assemble into a continuous map to the end space, so every multi-ended direction of a
  rigid action is amenable, boundary-type dynamics.
- Hence (RA), and its weaker form (RA'), which asks whether rigidity forces exactness and is all the
  Osajda question needs, reduce to **one-ended** groups.
- There, finite cuts give nothing, and Kazhdan groups have no walls either. A proof must find
  boundary structure without splittings, as the Ã₂ example does. A counterexample must live in a
  one-ended non-exact piece.
