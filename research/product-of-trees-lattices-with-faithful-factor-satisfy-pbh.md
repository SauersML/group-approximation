---
rg: 2
id: product-of-trees-lattices-with-faithful-factor-satisfy-pbh
kind: claim
title: A lattice in a finite product of locally finite trees lies in the permutational Boone--Higman class when some factor images separate points with finitely presented edge stabilizers
distinct_from:
  product-of-two-trees-lattices-satisfy-permutational-boone-higman: that covers every lattice in a product of two trees, one with more than two ends, with no faithfulness hypothesis, through generalized Baumslag--Solitar groups over F_2; this covers any number of factors under a hypothesis on the factor images.
  product-of-trees-lattices-satisfy-permutational-boone-higman: that is the open statement for all lattices in finite products of trees; this proves it under the separating-images hypothesis, in particular when one factor action is faithful.
  cat0-groups-satisfy-boone-higman: that is survey item (10) for all CAT(0) groups; this is one subclass.
---

**ESTABLISHED.** Let `n >= 1`, let `T_1, ..., T_n` be locally finite trees and
`X = T_1 x ... x T_n`. Let `Gamma` act on the vertices of `X` with finite vertex
stabilizers and finitely many vertex orbits. Each `gamma` acts by
`(x_1, ..., x_n) ↦ (gamma_1 x_(σ(1)), ..., gamma_n x_(σ(n)))` for some permutation
`σ = σ_gamma` and tree isomorphisms `gamma_j : T_(σ(j)) -> T_j`. Let:
- `Gamma_0` be the kernel of `gamma ↦ σ_gamma`, a subgroup of finite index;
- `pr_i : Gamma_0 -> Aut(T_i)` be the coordinate map, with kernel `K_i`.

`B_A` is the class of `boone-higman-type-a-class-closed-under-finite-extensions`.

1. **Finite presentation.** `Gamma_0` and `Gamma` are finitely presented.
2. **Separating factor images.** Suppose a set `I` of factors satisfies
   `∩_(i ∈ I) K_i = 1`, and for each `i ∈ I` the image `pr_i(Gamma_0)` has
   finitely presented edge stabilizers on `T_i`. Then `Gamma ∈ B_A`.
   - The stabilizer of an edge `e` in `pr_i(Gamma_0)` is `Gamma_(0,e) / K_i`,
     where `Gamma_(0,e)` is finitely presented.
   - So the hypothesis says that `K_i` is the normal closure in `Gamma_(0,e)` of
     finitely many elements.
3. **Faithful factor.** If `Gamma_0` acts faithfully on some `T_i`, then
   `Gamma ∈ B_A`.
4. **Quasi-centre criterion.** Suppose `Gamma_0` acts faithfully on `X`.
   - Give `H_i = ∏_(j ≠ i) Aut(T_j)` the topology of pointwise convergence on
     vertices.
   - Let `L_i` be the closure of the image of `Gamma_0` in `H_i`.
   - Then `K_i` maps injectively onto a discrete normal subgroup of `L_i`
     contained in the quasi-centre `QZ(L_i)`, the set of elements whose
     centralizer in `L_i` is open.
   - So if `QZ(L_i) = 1`, then `Gamma_0` is faithful on `T_i` and item 3
     applies.

In items 2 and 3, every subgroup of `Gamma` embeds in a finitely presented
simple group, and every finitely generated subgroup has solvable word problem.

**What is new.** For `n = 2`, item 3 is weaker than
`product-of-two-trees-lattices-satisfy-permutational-boone-higman`. The new
content is `n >= 3` and items 2 and 4.

Item 2 also covers products such as a Burger--Mozes lattice times a free group,
acting on three trees:
- on the Burger--Mozes lattice's first tree the kernel is the free factor;
- on the free group's tree the kernel is the lattice;
- the two kernels meet trivially.

**Credit.** Elementary once
`faithful-finite-index-graphs-of-groups-have-type-a-overgroups` is available. No
priority is claimed and no literature search was done beyond the BLIW paper.

Route: `product-of-trees-faithful-factor-pbh-via-bass-serre-induction`.
