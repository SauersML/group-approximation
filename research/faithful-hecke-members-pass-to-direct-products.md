---
rg: 2
id: faithful-hecke-members-pass-to-direct-products
kind: claim
title: Faithful one-vertex Hecke members pass to finite direct products, so BS_G lies in the permutational Boone--Higman class for every G virtually a product of free abelian groups and arithmetic lattices
distinct_from:
  arithmetic-lie-lattices-have-faithful-bs-members: that supplies faithful members for a single irreducible arithmetic lattice; this shows faithful members pass to direct products, covering reducible arithmetic lattices and mixed products such as Z^n x (surface group).
  bs-class-with-faithful-member-lies-in-type-a-class: that turns one faithful member into BS_G ⊆ B_A; this produces faithful members for products.
  boone-higman-type-a-class-closed-under-finite-extensions: that is closure of B_A under direct products of members; this is closure of the faithful-member property of the fibre group, a different statement, since BS_(G_1 x G_2) is not a class of products.
---

**ESTABLISHED** through `faithful-hecke-members-products-proof` (lane proof,
elementary; not independently reviewed; no priority claimed).

**Definition.** *Hecke data* on a group `G` is a finite family of injective
homomorphisms `φ_j : A_j → G` (`1 <= j <= r`), where `A_j` and `φ_j(A_j)` have finite
index in `G`. The *Hecke member* is

    H(G, φ) = ⟨ G, t_1, ..., t_r | t_j a t_j^{-1} = φ_j(a)  (a ∈ A_j) ⟩ ∈ BS_G.

**Criterion.** `H(G, φ)` acts faithfully on its Bass--Serre tree if and only if the
only normal subgroup `N` of `G` with `N ⊆ A_j` and `φ_j(N) = N` for every `j` is
`N = 1`.

**Products.** Let `(φ_j)` be faithful Hecke data on `G_1` and `(ψ_k)` faithful
Hecke data on `G_2`. Then the data `φ_j × id_(G_2)` on `A_j × G_2` and
`id_(G_1) × ψ_k` on `G_1 × B_k` is faithful Hecke data on `G_1 × G_2`.

**Consequence.** Let `G` be finitely presented and abstractly commensurable with
`G_1 × ... × G_m`, where each `G_i` is one of:
- free abelian of finite rank `>= 1`, with scaling data `x ↦ 2x`;
- an irreducible arithmetic lattice in a connected semisimple Lie group with trivial
  center and no compact factors, with the commensurator data of
  `arithmetic-lie-lattices-have-faithful-bs-members`, including free groups and
  closed surface groups;
- a definite quaternion lattice on two trees, as in instance 2 of
  `arithmetic-nsp-lattices-have-faithful-bs-members`.

Then `BS_G ⊆ B_A`. Examples: `S × S'` and `Z^n × S` for surface groups `S`, `S'`,
`F_2 × F_2 × Z`, and every reducible arithmetic lattice. By
`cat0-groups-with-a-tree-factor-lie-in-type-a-class`, every CAT(0) group on `Y × T`
whose tree-vertex stabilizer is of this form lies in `B_A`. One example is a group
acting geometrically on `H^2 × H^2 × T` whose fibre groups are virtually products of
two surface groups.
