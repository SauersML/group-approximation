---
rg: 2
id: exotic-a2-lattices-satisfy-boone-higman
kind: claim
title: Cocompact lattices on exotic A2-tilde buildings embed in finitely presented simple groups
distinct_from:
  cat0-groups-satisfy-boone-higman: that is item (10) for every CAT(0) group; this is the first named subclass on which every method on main fails at once.
  titz-witzel-simple-kazhdan-cat0-lattices-exist: that imports the non-residually-finite C2-tilde lattices and their simple finite-index kernels; this concerns lattices on exotic A2-tilde buildings, where no finite-index simple subgroup is known.
  char-zero-linear-groups-satisfy-permutational-boone-higman: that settles linear inputs; these lattices have no infinite linear image over any commutative ring.
---

**OPEN.** Let `X` be a locally finite Ã₂-building that isn't the building of
`PGL_3(D)`, and let `Gamma < Aut(X)` be discrete and cocompact. Then `Gamma`
embeds in a finitely presented simple group.

These lattices are CAT(0) groups, so this is a special case of
`cat0-groups-satisfy-boone-higman`.

## Why every method on main fails

1. **Linear hosts.** Bader--Caprace--Lécureux, arXiv:1608.06265, Theorem
   `nonlinear` (TeX l.185--190, verbatim): "Let $X$ be a locally finite
   $\widetilde A_2$-building and $\Gamma < \Aut(X)$ be a discrete group acting
   cocompactly. Assume that $X$ is not isomorphic to the building associated to
   $\mathrm{PGL}_3(D)$, with $D$ a finite dimensional division algebra over a
   local field. Then, for any commutative unital ring $R$ and any $n \geq 1$,
   any homomorphism $\Gamma \to \GL_n(R)$ has a finite image."
   - So the linear routes `char-zero-linear-groups-satisfy-permutational-boone-higman`
     and `char-p-linear-groups-satisfy-permutational-boone-higman` see only
     finite images.
2. **Tree hosts.** These lattices have property (T): Titz Mite--Witzel,
   arXiv:2509.05054v2 l.1700, for lattices on irreducible Euclidean buildings,
   citing unpublished work of Oppenheim; not independently pinned for Ã₂ here.
   - (T) gives FA, so a cocompact action on a locally finite tree forces a finite
     tree. BLIW Theorems B and C give nothing.
3. **Hyperbolic hosts.** `X` contains Euclidean planes, so `Gamma` isn't
   hyperbolic, and `hyperbolic-groups-satisfy-boone-higman` doesn't apply.
4. **Self-similar hosts** (`fp-self-similar-subgroups-satisfy-permutational-boone-higman`).
   A faithful action on a locally finite rooted tree forces residual finiteness.
   Titz Mite--Witzel l.194 record that "conjecturally none of them is residually
   finite", citing BCL Conjecture 1.5.
5. **MIF envelopes** (`fp-simple-highly-transitive-groups-satisfy-pbh`). This
   needs a finitely presented simple MIF overgroup. No simple group containing
   these lattices is known, and no mixed-identity statement for them was found.
   - BCL (TeX l.219) mention "an unpublished work of Yehuda Shalom and Tim Steger"
     showing "every non-trivial normal subgroup of a lattice in an
     $\widetilde{A}_2$-building is of finite index".
   - So if such a lattice is not residually finite, its finite residual is a
     finite-index subgroup with no nontrivial normal subgroup of infinite index.

## Exact gap

A finitely presented simple host must come from a new source. Candidates:
- boundary dynamics on the chamber space at infinity, a Cantor set, through a
  Brin--Thompson-like group of sector germs;
- a proof that some finite-index subgroup is MIF, together with a finitely
  presented simple overgroup.

## Attempt (2026-09-18, bh-groupoid): vertex-free type-transitive exotic lattices

*Reduced to the unpinned k-graph standard facts.*

- **Statement.** `type-transitive-vertex-free-a2-groups-embed-in-fp-simple-groups` covers
  every exotic lattice that acts freely on vertices with finitely many orbits, by type
  rotating automorphisms that are not all type preserving. This includes every CMSZ group,
  and so the 65 exotic order-3 buildings of CMSZ listed by BCL §`sec:ReviewExotic`.
  - Such a lattice embeds in a finitely presented simple group of type `F_∞`.
  - The only open input is `finite-k-graph-boundary-groupoid-standard-facts`.
- **Host.** This is the "boundary dynamics on the chamber space at infinity" candidate
  above, realized through the Robertson–Steger 2-graph groupoid and Li–Matui, with no sector
  germs.
- **Key steps** (lane proofs, not reviewed):
  - a geometric embedding into the 2-graph full group
    (`a2-group-embeds-in-rs-two-graph-geometric-proof`);
  - irreducibility and primitivity of the transition matrices by a local link argument
    (`a2-rs-matrices-irreducible-and-primitive-iff-type-transitive`);
  - aperiodicity from (H3) (`rs-two-graph-aperiodicity-from-h3-and-irreducibility`).
- **Not covered.** Lattices with torsion, and groups that are type preserving with no
  type-transitive overgroup, stay open here.

**Update (2026-09-18, later).** `finite-k-graph-boundary-groupoid-standard-facts` is now
proved (`finite-k-graph-standard-facts-proof`, lane proof). So
`type-transitive-vertex-free-a2-groups-embed-in-fp-simple-groups` is ESTABLISHED (lane
proofs, unreviewed).
- **Covered.** Every exotic Ã₂ lattice acting freely and with finitely many orbits on
  vertices by type rotating automorphisms that are not all type preserving embeds in a
  finitely presented simple group of type `F_∞`. This includes the vertex-regular lattices
  of the 65 exotic CMSZ buildings of order 3, and all their subgroups.
- **Still open.** This node stays OPEN for exotic lattices with torsion, and for groups that
  are type preserving with no type-transitive overgroup.

**Update (2026-09-18, final).** The type-preserving case is also done:
`type-preserving-vertex-free-a2-groups-embed-in-fp-simple-groups` (lane proof).
- **Covered.** Every lattice acting freely on the vertices of an exotic Ã₂ building by type
  rotating automorphisms now embeds in a finitely presented simple group
  (`vertex-free-type-rotating-a2-groups-satisfy-boone-higman`, ESTABLISHED as lane proofs).
- **Still open.** Lattices with torsion, that is, with nontrivial vertex stabilizers. The
  gap is exactly the non-free case.
