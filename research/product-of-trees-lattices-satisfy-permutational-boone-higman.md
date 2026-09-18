---
rg: 2
id: product-of-trees-lattices-satisfy-permutational-boone-higman
kind: claim
title: Every group acting on a finite product of locally finite trees with finite vertex stabilizers and finitely many vertex orbits lies in the permutational Boone--Higman class
distinct_from:
  product-of-trees-lattices-with-faithful-factor-satisfy-pbh: that proves this when some set of factor images separates points and has finitely presented edge stabilizers; this is the statement with no such hypothesis.
  product-of-two-trees-lattices-satisfy-permutational-boone-higman: that is the case of two factors, one with more than two ends; this allows any number of factors.
  cat0-groups-satisfy-boone-higman: that is survey item (10) for all CAT(0) groups; this is the product-of-trees subclass.
---

**OPEN.** Setting and notation (`Gamma`, `Gamma_0`, `pr_i`, `K_i`) as in
`product-of-trees-lattices-with-faithful-factor-satisfy-pbh`, with any
`n >= 1`. Then `Gamma ∈ B_A`.

**Established cases.**
- Two factors, one with more than two ends:
  `product-of-two-trees-lattices-satisfy-permutational-boone-higman`.
- Any `n`, when a set `I` of factors has `∩_(i ∈ I) K_i = 1` and finitely
  presented edge stabilizers in each image `pr_i(Gamma_0)`. This includes every
  lattice with a faithful factor, and every lattice acting faithfully on `X`
  with `QZ(L_i) = 1` for some `i`: items 2–4 of
  `product-of-trees-lattices-with-faithful-factor-satisfy-pbh`.

## Attempts

1. **Faithful or separating factors.** *Works.* See the established cases
   above (2026-09-13).
2. **Direct products.** *Works when the pieces are covered.* If `Gamma_0` is
   virtually a direct product of lattices on complementary sets of factors, each
   covered by the cases above, item 1 of
   `boone-higman-type-a-class-closed-under-finite-extensions` covers `Gamma`.
   This is not written as a separate node.
3. **No separating set of factors.** *Open.*
   - **Exact gap.** For every set `I` with `∩_(i ∈ I) K_i = 1`, some `K_i` with
     `i ∈ I` is not the normal closure of finitely many elements in the edge
     stabilizers `Gamma_(0,e)`.
   - **Why BLIW's methods stop here.** Under a faithful action on a locally
     finite tree, vertex stabilizers are residually finite. This is recorded in
     the scope paragraph of
     `bliw-locally-finite-tree-actions-embed-in-fp-simple-groups`.
     - The `Gamma_0`-stabilizers of vertices of `T_i` are lattices in the other
       factors, and these can fail to be residually finite: Burger--Mozes and
       Wise lattices, per the two-tree node; not re-checked here.
     - When they fail, `T_i` can't be a faithful factor.
     - The enlargement in BLIW Theorem 11.1 needs a faithful group commensurable
       with such a stabilizer. That group would have to be residually finite, so
       the enlargement is blocked too.
   - **Quasi-centres.** By item 4 of the established claim, any counterexample
     acting faithfully on `X` has `QZ(L_i) ≠ 1` for every `i`.
   - **Not examined.** Whether an irreducible lattice in three or more trees
     with non-trivial kernel on every factor exists at all.
4. **Discrete factor images (bh-lattices, 2026-09-18).** *Works for three
   factors.* `discrete-factor-tree-lattices-are-virtually-products`:
   if some `pr_i(Gamma_0)` is discrete, then `K_i` is a lattice on the other
   factors and `Gamma_0` is virtually `K_i x F` with `F` free. For `n = 3` this
   puts `Gamma` in `B_A` via the two-tree node. So a three-tree counterexample
   must have, for every `i`: `pr_i(Gamma_0)` non-discrete, `K_i` infinite, and
   `K_i` an infinite normal subgroup of infinite index in the two-tree fibre
   lattice `H_i`, which therefore fails every normal subgroup theorem.
   - **Refines "Not examined".** A lattice with non-trivial kernel on every
     factor and some discrete factor image is always virtually a product. The
     question is now only about totally non-discrete lattices whose fibres
     violate the normal subgroup property. No example of either kind is known
     to this lane.
