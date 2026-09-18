---
rg: 2
id: cubical-hecke-members-faithful-when-closure-fixes-bounded-sets
kind: claim
title: A Hecke HNN extension of a discrete torsion-free group of cube-complex automorphisms acts faithfully on its Bass--Serre tree when the closure of the group and its commensurator letters has no open subgroup fixing a point at infinity
distinct_from:
  arithmetic-lie-lattices-have-faithful-bs-members: that works in a Lie group and kills the kernel with Borel density; this works in the totally disconnected group Aut(Y) of a locally finite CAT(0) cube complex and kills the kernel with the quasi-centre, through bounded fixed sets of compact open subgroups.
  commensurator-rigid-groups-lack-faithful-bs-members: that shows discrete commensurators give no faithful member; this gives a faithful member whenever the closure is large in the sense (FB), which forces it to be non-discrete.
  three-tree-lattices-escape-only-via-discrete-normal-subgroups: that asks for trivial quasi-centre of single-tree closures inside a three-tree lattice; this is a criterion for any locally finite CAT(0) cube complex, applied to the closure of the whole commensurator extension.
---

**ESTABLISHED** through `cubical-hecke-members-faithful-proof` (lane proof,
elementary; not independently reviewed; no priority claimed).

**Setting.**
- `Y` is a locally finite CAT(0) cube complex and `A = Aut(Y)` with the
  permutation (compact-open) topology. `A` is totally disconnected and locally
  compact, and every vertex stabilizer `A_y` is compact and open.
- `G <= A` is discrete and torsion-free, so it acts properly on `Y`.
- `c_1, ..., c_m ∈ Comm_A(G)`. Put `G_i = G ∩ c_i^{-1} G c_i` (finite index in
  `G`) and `φ_i(h) = c_i h c_i^{-1}`, an isomorphism onto `G ∩ c_i G c_i^{-1}`.
- `M = G *_{φ_1, ..., φ_m}` is the multiple HNN extension (one vertex `G`, loops
  with edge groups `G_i`). It lies in `BS_G` (`bs-class-with-faithful-member-lies-in-type-a-class`).
- `L` is the closure of `<G, c_1, ..., c_m>` in `A`.

**Condition (FB).** Every compact open subgroup of `L` has a bounded fixed-point
set in `Y`. For proper CAT(0) spaces this is equivalent to: no open subgroup of
`L` fixes a point of the visual boundary `∂Y`. It forces `L` to be non-discrete,
since in a discrete `L` the trivial subgroup is open and fixes all of `Y`.

**Theorem.**
1. If `L` satisfies (FB), then `M` acts faithfully on its Bass--Serre tree.
2. More generally, without assuming (FB) or torsion-freeness: if `L` has no
   nontrivial discrete normal subgroup contained in `G` (for instance if the
   quasi-centre `QZ(L)` is trivial), then `M` is faithful.
3. **Consequence for Boone--Higman.** If moreover `G` is finitely presented (for
   instance if `G` acts cocompactly on `Y`), then `BS_G ⊆ B_A` by
   `bs-class-with-faithful-member-lies-in-type-a-class`. In particular `G` itself,
   a member of `BS_G`, embeds in a finitely presented simple group.
4. **Residual finiteness is forced.** A faithful member acts faithfully on a
   locally finite tree with `G` as a vertex stabilizer, so `G` embeds in a
   profinite group and is residually finite. Hence for a discrete torsion-free
   `G <= Aut(Y)` that is **not** residually finite, every closure
   `closure<G, c_1, ..., c_m>` with `c_i ∈ Comm_A(G)` has an open subgroup fixing a
   point of `∂Y`.

**Calibration.**
- Discrete commensurators never satisfy (FB), matching
  `commensurator-rigid-groups-lack-faithful-bs-members`.
- Item 4 matches the remark of Bux--Llosa Isenrich--Wu that base groups of faithful
  members must be residually finite.
- For `Y` a regular tree `T_d`, `d >= 3`, the full group `Aut(T_d)` satisfies (FB):
  the fixator of a ball fixes only that ball, since each boundary vertex of the
  ball has at least two children that can be swapped. So any `c_i` with
  `closure<G, c_i> = Aut(T_d)` give faithful members for `G = F_k`, consistent with
  BLIW Theorem 12.5.
- For `Y = T_1 × T_2` a product of regular trees, `Aut(T_1) × Aut(T_2)` satisfies
  (FB) the same way, using products of ball fixators.

**Scope.**
- The argument uses only that `A` is totally disconnected with compact open point
  stabilizers and that `Y` is proper CAT(0). It works verbatim for locally finite
  polyhedral CAT(0) complexes with finitely many shapes.
- It does not decide when (FB) holds for a given closure. By Caprace--Monod
  (arXiv:0809.0457, Corollary `cor:NoOpenStabiliser`(iv), read at source) (FB)
  implies `QZ(L) = 1` for geodesically complete `Y` without Euclidean factor. Item 1
  is proved directly here, without geodesic completeness.
