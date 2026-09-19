---
rg: 2
id: building-transplants-pass-the-separability-test
kind: claim
title: In a Busemann transplant over a Euclidean building lattice, changing the chamber at infinity changes the sector germ at every vertex of every apartment containing both chambers, so every skeleton modification reaches every horospherical level; the Ã2 transplants pass the separability test whenever their fibre does
distinct_from:
  tree-product-transplants-pass-the-separability-test: that handles products of trees, where an end change flips pointers on a line times the other tree, and leaves the building case open; this settles the building case, where a chamber change moves the germ on a whole apartment.
  a2-busemann-transplants-preserve-quantum-rigidity: that proves rigidity from rigidity of the fibre; this checks the classical necessary condition independently, for the pairs the skeleton adds.
---

**ESTABLISHED** (lane bh-free-09, 2026-09-18; elementary lane proof, not independently reviewed; no
priority claimed). It answers the open check of `tree-product-transplants-pass-the-separability-test`.

## Setting

The Setting of `busemann-transplants-give-free-sfts-on-building-lattices`:
- `Γ` acts simply transitively on the special vertices `V_0` of one type of a thick Euclidean building
  `Δ` (`Ã₂` included).
- The skeleton is the radius-`K` sector coding `x_c(γ) = γ^(-1)·(Q(γo, c) ∩ B(γo, K))`, with `K >= 1`,
  possibly with a phase coordinate in `L/nL`.
- The tile at `v` is read at `M^(-1) b_c(v)`.

## Theorem

Let `c ≠ c'` be chambers at infinity, and let `A` be any apartment whose boundary contains both.
1. **The germ changes on a whole apartment.** For every `v ∈ A ∩ V_0`, `x_c(v) ≠ x_(c')(v)`.
2. **Busemann surjectivity.** `b_c(A ∩ V_0)` is the full coset `b_c(V_0)` of `L`.
3. **Consequences.** Items 3 and 4 of `tree-product-transplants-pass-the-separability-test` hold
   verbatim:
   - every skeleton modification meets every other modification of the same point;
   - pure fibre modifications are unions of `b_c`-fibres;
   - the distances between such unions are comparable to the distances of their images in `L`.

   So the transplant has a separable pair of modifications only if its fibre does. With the minimal
   crossing-wire fibre (`crossing-wire-shifts-pass-the-separability-test`), **the `Ã₂` transplants of
   bh-invent-04 pass the separability test.**

## Proof

- **Item 1.** `v ∈ A` and `c, c' ∈ ∂A`, so both sectors `Q(v, c)` and `Q(v, c')` lie in `A`. They are
  the translates to `v` of two distinct Weyl chambers of the vector space of `A`. So their chambers at
  `v` differ, and those chambers lie in `B(v, 1) ⊆ B(v, K)`.
- **Item 2.** On an apartment containing `c`, the vector Busemann function `b_c` is, up to a
  translation, the affine coordinate of `A`. It maps the special vertices of the given type onto one
  coset of `L`. By (Onto) of `busemann-transplant-minimality-is-horospherical-minimality`, this is
  the full coset `b_c(V_0)`.
- **Phases.** A modification that changes only the phase coordinate changes it at every vertex, so it
  is surjective trivially.
- **Item 3, skeleton pairs.** Two chamber changes `c → c'` and `c → c''` give apartments
  `A' ⊇ Q(v, c)` and `A'' ⊇ Q(w, c)`. Two sectors toward one chamber share a subsector, so the two
  difference sets share vertices.
- **Item 3, the other pairs.**
  - *Skeleton against fibre.* A fibre modification is a union of whole `b_c`-fibres. By item 2 each
    of those fibres meets `A' ∩ V_0`.
  - *Fibre against fibre.* `b_c` is 1-Lipschitz for the building metric, since retraction onto an
    apartment containing `c` does not increase distances. Every vertex lies in an apartment containing
    `c`, and there every lattice step lifts to a path of comparable length. The word metric of `Γ` is
    quasi-isometric to the building metric on `V_0`, and separability is invariant under
    quasi-isometry. `∎`

## Lesson for general BH

- **In buildings, the boundary is a Busemann-surjective skeleton.** A change of the chamber at infinity
  is never local. It moves the germ on a whole apartment, which crosses every horosphere.
- **So transplants can fail only in the fibre.** With the Ã₂ and tree cases both checked, every
  transplant on main (tree products, BMW groups, Ã₂ lattices) passes the classical necessary
  condition exactly when its `Z²` fibre does.
- **What rigidity still has to prove.** It is the quantum content: (C), which bh-invent-04 proves by
  cylinder transport. No classical freedom obstructs it.
