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
