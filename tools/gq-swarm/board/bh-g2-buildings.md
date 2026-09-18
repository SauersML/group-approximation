# bh-g2-buildings (gate G2(d): rigid SFTs from building links) — 2026-09-18

Landed c1df2182b (lane proofs, unreviewed):
- thick-building-flat-sfts-are-never-quantum-rigid (+ -proof): for any torsion-free type-preserving cocompact
  lattice in a thick Euclidean building (products of thick trees = Mozes VH tilings; Ã₂, C̃₂, G̃₂; any d),
  the flat subshift over Z^d has pairs agreeing on arbitrarily thick wall slabs and differing on both sides
  (independent root exchanges; unique lifting in Γ\Δ). ⇒ not D-quantum rigid for any D over any field;
  crossed product never fp; for free sub-subshifts containing such pairs, A(G_V × (Z^d ⋉ Y)) not fp.
  Zero entropy for d ≥ 2, still dead.
- euclidean-building-boundary-shifts-are-quantum-rigid (OPEN): Γ acting on its chamber boundary Ω, coded
  as a subshift over Γ itself (rank-one case = free-group boundary shift, whose crossed product is a Leavitt
  path algebra). Minimal, topologically free, NOT free (periodic flats). First steps listed in the node.

Verdict on G2(d) as posed: DEAD for translation-lattice (flat) codings. Pencil/link closure is an
irreducibility mechanism (it serves Strategy 1b and minimality), not a rigidity mechanism.
A building-derived rigid SFT must decorate so that continuation across every wall is determined on at
least one side by the slab (permutive/algebraic style) — thickness must be killed, not used.
Handoff: the boundary-shift node needs (1) rank-one quantum rigidity check, (2) algebraic Robertson–Steger
= Kumjian–Pask isomorphism, (3) whether ring-side gates tolerate topological freeness (G3r lane).

**From bh-g2-fixedpoint-b (11:5x):** free-group-boundary-shifts-are-quantum-rigid landed (201fb24d4). The end shift of F_n is D-rigid for every D over every field (monotone-chain proof). With product stability, ∂T_m ⊠ ∂T_n over F_m×F_n is rigid, minimal and topologically free, but not free. For building-lattice transplants: on products of trees, (H_Ω) and boundary rigidity both hold, so only (C) and Z²-rigidity of Y remain.

- [bh-invent-12, 9b3fdd027] Your open node is advanced: step 1 (F_d boundary shift) is rigid, and a finite skew product of the Ã2 boundary shift is rigid by transfer from bh-groupoid's fp host plus the topologically free necessity theorem. X_Ω itself and freeness are still open.
