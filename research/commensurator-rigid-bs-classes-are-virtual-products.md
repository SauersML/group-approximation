---
rg: 2
id: commensurator-rigid-bs-classes-are-virtual-products
kind: claim
title: For a group of finite index in its abstract commensurator, every virtually torsion-free member of its Baumslag--Solitar class is virtually a product with a virtually free group
distinct_from:
  commensurator-rigid-groups-lack-faithful-bs-members: that proves such members with torsion-free vertex groups are never faithful; this upgrades the kernel it finds to a structure theorem, virtually N x F, and extends it to all virtually torsion-free members.
  bs-class-with-faithful-member-lies-in-type-a-class: that is the positive route through a faithful member; this handles the classes where that route is provably void, by linearity instead.
---

**ESTABLISHED** through `commensurator-rigid-bs-products-proof` (lane proof,
elementary given the obstruction node; not independently reviewed; no priority
claimed).

**Hypotheses.** As in `commensurator-rigid-groups-lack-faithful-bs-members`:
- `G` is finitely generated and torsion-free;
- `VZ(G) = 1`;
- `G` has finite image-index in its abstract commensurator `Comm(G)`.

**Theorem.** Let `H ∈ BS_G` be virtually torsion-free. Then:
1. `H` has a finite-index subgroup `H_2 ≅ N × F`, where `N` is a finite-index
   subgroup of a vertex group, hence commensurable with `G`, and `F` is finitely
   generated and virtually free;
2. `H` does not act faithfully on its Bass--Serre tree;
3. if some finite-index subgroup of `G` lies in `B_A`, then `H ∈ B_A`. This holds,
   for instance, when `G` is linear in characteristic zero.

**Instances.** Torsion-free lattices `G` in `Isom(X)`, for `X` an irreducible
symmetric space of noncompact type other than `H^2`, whose commensurator in
`Isom(X)^0` is discrete. By Mostow--Prasad rigidity the abstract commensurator is
the commensurator in `Isom(X)`, which then contains `G` with finite index. By
Margulis's criterion these are exactly the non-arithmetic lattices; that criterion
is not needed here.
