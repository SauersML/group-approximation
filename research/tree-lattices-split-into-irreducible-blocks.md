---
rg: 2
id: tree-lattices-split-into-irreducible-blocks
kind: claim
title: A faithful cocompact lattice on a product of leafless trees is virtually the direct product of irreducible blocks, one for each piece of a partition of the factors
distinct_from:
  discrete-factor-tree-lattices-are-virtually-products: that splits off one tree whose image is discrete and allows a finite kernel; this splits along any sub-product whose image is discrete, for faithful lattices, and iterates to a block decomposition.
  product-of-trees-lattices-with-faithful-factor-satisfy-pbh: that needs trivial kernels on some factors; this produces the blocks whose kernels are the obstruction.
---

**ESTABLISHED** through `tree-lattice-block-splitting-proof` (lane proof,
elementary; not independently reviewed; no priority claimed).

**Setting.** `T_1, ..., T_n` are locally finite leafless trees (every vertex has
degree at least 2), each infinite, and `X = T_1 x ... x T_n`. `Γ <= Aut(X)`
acts with finite vertex stabilizers and finitely many vertex orbits. (So `Γ`
acts faithfully; this is a cocompact lattice in `Aut(X)`.) `Γ_0` is the finite
index subgroup preserving every factor. For `I ⊆ [n]` write `X_I = ∏_(i ∈ I) T_i`,
`pr_I : Γ_0 -> Aut(X_I)`, and `K_I = ker pr_I`.

1. **Splitting.** If `pr_I(Γ_0)` is discrete for some `∅ ≠ I ⊊ [n]`, then
   `pr_(I^c)(Γ_0)` is discrete too, `K_I` and `K_(I^c)` are faithful cocompact
   lattices on `X_(I^c)` and `X_I` respectively, and `K_I x K_(I^c)` is a
   subgroup of finite index in `Γ_0`.
2. **Blocks.** Call `Γ` *irreducible* if no proper nonempty `I` has
   `pr_I(Γ_0)` discrete. Iterating item 1, some finite-index subgroup of `Γ_0`
   is a direct product `Λ_1 x ... x Λ_r` of irreducible faithful cocompact
   lattices `Λ_s` on `X_(I_s)`, for a partition `[n] = I_1 ⊔ ... ⊔ I_r`.
3. **Consequence.** If every block `Λ_s` lies in `B_A`, so does `Γ`
   (`boone-higman-type-a-class-closed-under-finite-extensions`, items 1 and 2).
   Blocks on one tree are virtually free, hence in `B_A`; blocks on two trees are
   in `B_A` by `product-of-two-trees-lattices-satisfy-permutational-boone-higman`.

**Leafless.** A cocompact action on a leafless locally finite tree is minimal
(see the route). Pruning leaves may create a finite kernel, which item 1 does not
allow; `discrete-factor-tree-lattices-are-virtually-products` handles that case
for single factors.
