---
rg: 2
id: commensurator-rigid-groups-lack-faithful-bs-members
kind: claim
title: If a torsion-free group has finite index in its abstract commensurator, no member of its Baumslag--Solitar class with torsion-free vertex groups acts faithfully; so for lattices in Isom(H^n), n >= 3, such faithful members exist exactly for arithmetic lattices
distinct_from:
  commensurator-rigid-groups-have-no-faithful-bs-members: that (bh-free-22, fb1c469c2) proves the stronger statement, no faithful member at all, including members with torsion in the vertex groups, assuming only that G -> Comm(G) is injective with finite-index image; this is the earlier torsion-free-vertex case, kept for its explicit pull-back construction.
  arithmetic-lie-lattices-have-faithful-bs-members: that is the positive half, faithful Hecke members for arithmetic lattices; this is the matching obstruction, which kills the Bux--Llosa Isenrich--Wu Theorem C route with torsion-free vertex groups for non-arithmetic rank-one lattices.
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that records the authors' stated obstruction, that G must be residually finite; this is a second, independent obstruction for residually finite G.
  hyperbolic-groups-satisfy-boone-higman: that settles Boone--Higman for the lattices themselves; this concerns graphs of groups commensurable with them, where no method on main applies once the tree route is dead.
---

**ESTABLISHED** through `commensurator-finite-no-faithful-bs-proof` (lane proof;
referee a PASS,
`research/artifacts/gq-referee-a-hecke-products-and-commensurator-rigidity.md`;
no priority claimed).

**Notation.**
- For a group `V`, `VZ(V)` is its virtual center: the elements centralizing a
  finite-index subgroup.
- `Comm(V)` is the abstract commensurator: isomorphisms between finite-index
  subgroups, modulo agreement on a finite-index subgroup.
- `BS_G` is as in `bs-class-with-faithful-member-lies-in-type-a-class`.

**Theorem.** Let `G` be a finitely generated, torsion-free group with
`VZ(G) = 1`, whose image under `G → Comm(G)`, `g ↦ [conj_g]`, has finite index.
Let `H ∈ BS_G` be the fundamental group of a finite graph of groups whose vertex
groups are torsion-free. Then `H` does not act faithfully on its Bass--Serre tree.

**Instances.** Torsion-free non-arithmetic lattices `G` in `PO(n,1)^0`, `n >= 3`,
and in `PU(n,1)`, `n >= 2`, such as the Gromov--Piatetski-Shapiro and
Deligne--Mostow lattices.
- By Mostow--Prasad rigidity, every isomorphism between finite-index subgroups is
  conjugation by an isometry. So `Comm(G) ≅ Comm_L(G)`.
- By Margulis, `Comm_L(G)` is discrete for non-arithmetic `G`, so it contains `G`
  with finite index.
- `VZ(G) = 1` by Borel density.

**Dichotomy.** Let `G` be a torsion-free lattice in `PO(n,1)^0`, `n >= 3`. Then `BS_G`
has a member with torsion-free vertex groups acting faithfully on its tree if and
only if `G` is arithmetic.
- For "if": `arithmetic-lie-lattices-have-faithful-bs-members` gives a Hecke member
  whose single vertex group is `G`.
- For "only if": the theorem.

**Consequence for the Theorem C route.** Bux--Llosa Isenrich--Wu Theorem C needs one
faithful `H ∈ BS_G`. For non-arithmetic `G` as above, such an `H` must have torsion
in some vertex group. Every faithful member they construct, and every Hecke member
here, has torsion-free vertex groups when `G` is torsion-free. Members with torsion in their vertex groups are excluded too, by
`commensurator-rigid-groups-have-no-faithful-bs-members`, so the dichotomy holds
without the torsion-free qualifier.

**Calibration.**
- For `F_k` and surface groups, `Comm` is far larger than `G`, and faithful members
  exist.
- For `Z^n`, `VZ = Z^n`, and scaling members exist.
- Both are consistent with the theorem, whose hypotheses fail in these cases.
