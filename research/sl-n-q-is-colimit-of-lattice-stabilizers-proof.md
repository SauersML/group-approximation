---
rg: 2
id: sl-n-q-is-colimit-of-lattice-stabilizers-proof
kind: route
title: Present each SL_n(Z[1/S]) by Brown's theorem on the staircase-triangulated product of buildings, then take the union over S
target: sl-n-q-is-colimit-of-lattice-stabilizers
requires: []
artifacts:
  - research/artifacts/gq-referee-b-sl-n-q-is-colimit-of-lattice-stabilizers.md
---

Fix a finite set `S` of primes. Put `Γ_S = SL_n(Z[1/S])`, `G_S = ∏_{p∈S} SL_n(Q_p)`,
`X_S = ∏_{p∈S} X_p` (the product of the Bruhat–Tits buildings) and
`C_S = ∏_{p∈S} Δ_p` (the product of the standard chambers).

**Imports (literature).**
- **(I2) Euclidean buildings are CAT(0).** L. Kramer, arXiv:1009.3089, §6.4(a),
  read on ar5iv and not cross-checked against the PDF: "A euclidean building is a
  (not necessarily complete) CAT(0) space." Bridson–Haefliger II.10A.4 gives the
  same fact; not read at source.
- **(I3) Presentations from a strict fundamental domain.** K. S. Brown,
  J. Pure Appl. Algebra 32 (1984), Theorem 1′. It is transcribed in
  arXiv:2603.25586, Theorem 2.1; the primary was not read. Let `G` act on a
  **simplicial** complex `K` with a subcomplex `W` such that (1) `K` is simply
  connected, (2) each simplex of `K` is equivalent mod `G` to a unique simplex of
  `W`, (3) `W` has finite 2-skeleton, (4) vertex stabilizers are finitely
  presented and (5) edge stabilizers are finitely generated. Then `G` is the
  amalgam of the vertex stabilizers of `W` along its edge stabilizers.
  Soulé (C. R. Acad. Sci. Paris 276 (1973)) and Bridson–Haefliger II.12.22 are
  secondary pointers, not read.

**Step 1 (density and orbits).** `Z[1/S]` is dense in `∏_{p∈S} Q_p` (CRT). So the
closure of `Γ_S` in `G_S` contains the product root groups, which generate
`E_n(∏_p Q_p) = ∏_p SL_n(Q_p) = G_S`. Cell stabilizers of `X_S` in `G_S` are open,
so `Γ_S` and `G_S` have the same orbits on cells.

**Step 2 (strict fundamental domain).** `SL_n(Q_p)` preserves types and is
transitive on chambers, so every face of `X_p` is equivalent to exactly one face
of `Δ_p`. By step 1, `C_S` is a strict fundamental domain for `Γ_S` on `X_S`, and
a type-preserving element stabilizing a cell fixes it pointwise.
- The stabilizer of a lattice class in `SL_n(Q_p)` is the stabilizer of the
  lattice, since `gL = p^m L` forces `v_p(det g) = mn`.
- A lattice in `Q^n` is determined by its localizations, and
  `L_c ⊗ Z_p = Z_p^n` for `p ∉ S`.
- So the vertex stabilizers in `Γ_S` of `C_S` are the `Γ_c` with all `c_i`
  supported on `S`, and cell stabilizers are the `Γ_F`.

**Step 3 (contractibility).** A CAT(0) space is contractible. Fix `x_0` and let
`H(y,t)` be the point at fraction `t` along the geodesic from `y` to `x_0`. The
CAT(0) inequality gives `d(H(y,t),H(y',t)) <= (1-t)d(y,y')`, so `H` is continuous.
Each `X_p` is locally finite, so its metric and CW topologies agree, and `X_S` is
contractible, in particular simply connected.

**Step 4 (staircase triangulation; amendment A1).** For `|S| >= 2`, `X_S` is
polysimplicial, not simplicial. The types `{0,...,n-1}` totally order the vertices
of each simplex of `X_p`.
- Triangulate `X_S` by the staircase (Eilenberg–Zilber) triangulation `K`: the
  same vertices, and as simplices the chains in the coordinatewise order inside a
  product cell.
- `Γ_S` preserves types, so it acts simplicially on `K`, and the triangulated
  `C_S` is a subcomplex `W`.
- Hypothesis (2): every simplex `τ` has a smallest carrier cell `σ(τ)`. If `τ`
  and `gτ` both lie in `W`, then `σ(τ)` and `gσ(τ)` are faces of `C_S`. By step 2
  they are equal and `g` fixes `σ(τ)` pointwise, so `gτ = τ`.
- (1) is step 3; (3) holds since `W` is finite; (4) holds since `Γ_c ≅ SL_n(Z)`
  is finitely presented; (5) holds since edge groups have finite index in
  vertex groups.
- By (I3), `Γ_S` is the amalgam of the `Γ_c` along the edge groups `Γ_{F(c,c')}`.
  This equals the colimit over all cells of `C_S`. Every cell relation
  `Γ_F ⊆ Γ_c, Γ_F ⊆ Γ_c'` factors along an edge path from `c` to `c'` inside `F`,
  with `Γ_F` contained in each edge group on that path. Conversely each staircase
  edge relation is the relation of the cell `F(c,c')`. So the maps between the two
  colimits, induced by the vertex groups, are mutually inverse.

**Step 5 (union over S).** The faces of `C_S` are the cells with `F_p = {0}` for
`p ∉ S`, with the same groups `Γ_F = ∩ Γ_c`. The poset of all cells is the
directed union of these, and every relation among cells involves finitely many
primes. So the colimit over all cells is `colim_S Γ_S = ∪_S Γ_S = SL_n(Q)`. ∎
