---
rg: 2
id: commensurator-rigid-bs-classes-are-virtual-products
kind: claim
title: For a group of finite index in its abstract commensurator, every member of its Baumslag--Solitar class is virtually a product with a free group
distinct_from:
  commensurator-rigid-groups-lack-faithful-bs-members: that proves such members with torsion-free vertex groups are never faithful; this upgrades the kernel to a structure theorem, virtually N x F, for every member.
  commensurator-rigid-groups-have-no-faithful-bs-members: that (bh-free-22) proves every member has a kernel of finite index in the vertex groups; this consumes it and identifies the whole group up to finite index.
  bs-class-with-faithful-member-lies-in-type-a-class: that is the positive route through a faithful member; this handles the classes where that route is provably void, by passing to the kernel instead.
---

**ESTABLISHED** through `commensurator-rigid-bs-products-proof` (lane proof,
elementary given `commensurator-rigid-groups-have-no-faithful-bs-members`; not
independently reviewed; no priority claimed).

**Hypotheses.** `G` is finitely generated and infinite. The map
`G → Comm(G)`, `g ↦ [conj_g]`, is injective (equivalently `VZ(G) = 1`) and has
image of finite index.

**Theorem.** Let `H ∈ BS_G`, and let `K` be the kernel of `H` on its Bass--Serre
tree. Then:
1. `K` has finite index in every vertex group, so it is commensurable with `G`;
2. `H` has a finite-index subgroup `K × F`, with `F` free of finite rank;
3. if some finite-index subgroup of `G` lies in `B_A`, then `H ∈ B_A`. This holds,
   for instance, when `G` is linear in characteristic zero.

**Instances.**
- Torsion-free lattices `G` in `Isom(X)`, for `X` an irreducible symmetric space of
  noncompact type other than `H^2`, whose commensurator in `Isom(X)^0` is discrete.
  By Mostow--Prasad the abstract commensurator is the commensurator in `Isom(X)`,
  which then contains `G` with finite index.
- `Out(F_n)`, `n >= 4`, and closed mapping class groups, by the instances of
  `commensurator-rigid-groups-have-no-faithful-bs-members`. There item 3 would need
  a finite-index subgroup in `B_A`, which is open.
