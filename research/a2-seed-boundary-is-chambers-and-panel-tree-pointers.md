---
rg: 2
id: a2-seed-boundary-is-chambers-and-panel-tree-pointers
kind: claim
title: Every point of the Ã2 origin-projection seed is an origin field, a chamber field toward a chamber at infinity, or a wall field given by a pointer toward one vertex of the panel tree of a vertex at infinity; so the seed's boundary is exactly the chamber stratum and the panel-tree wall strata
distinct_from:
  a2-lattices-carry-finite-type-seeds: that proves the seed axioms and leaves the boundary undescribed; this classifies all its boundary points.
  a2-phase-seed-passes-the-separability-test: that uses this classification (its description (S)) to prove the classical necessary condition for rigidity; this proves (S).
  a2-lattice-phase-seeds-are-quantum-rigid: that is the open quantum rigidity of the seed, whose What remains item 1 conjectures this description of the wall strata; this proves it.
---

**ESTABLISHED** through `a2-seed-boundary-pointer-proof` (lane bh-free-09, 2026-09-19; elementary lane
proof, not independently reviewed; no priority claimed).

It rests on standard facts about Euclidean buildings, recalled and not re-read. These are the
horofunction boundary of the building's graph metric in this special case.
- Ciobotaru–Kramer–Schwer (arXiv:2002.12422, Adv. Geom. 2023) treat the vector-space case in general.
  Their building sequel is "in preparation", checked at source on 2026-09-19.
- So no building-level theorem is cited.

## Setting

Notation is that of `a2-lattices-carry-finite-type-seeds`:
- `Δ` is a locally finite thick `Ã₂` building of order `q`;
- `a_o(x)` is the simplex of `Lk(x)` containing the germ of `[x, o]`;
- `Y_Γ` is the origin-projection seed, and its points are `Γ`-coded label fields `x ↦ y(x) ∈ Lk(x) ∪ {*}`.

Phases are ignored: the phase seed factors onto `Y_Γ`.

**Recalled facts** (standard, not re-derived):
- (B1) Sectors lie in apartments.
- (B2) Any two simplices, or a simplex and a chamber at infinity, lie in a common apartment.
- (B3) `Δ ∪ ∂Δ` is compact in the cone topology.
- (B4) Upper semicontinuity of angles: if `o_n → η`, then at each `x` the direction of `[x, o_n]`
  converges to that of `[x, η)`.
- (B5) The panel tree `T_ξ` of a vertex `ξ ∈ ∂Δ` (Tits, *Immeubles de type affine*, LNM 1181).
  - Its vertices are the classes of rays from vertices toward `ξ`, where two rays are equivalent when
    they eventually coincide. `π_ξ(x)` is the class of the ray from `x`.
  - It is a tree. For each apartment `A` with `ξ ∈ ∂A`, `π_ξ` maps `A` onto a geodesic line of `T_ξ`,
    sending `ξ`-lines of `A` at transverse lattice distance `k` to vertices at distance `k`, and every
    edge of `T_ξ` lies on such a line.
  - The two ends of that line are the two chambers of `∂A` through `ξ`. This gives a bijection between
    ends of `T_ξ` and chambers at infinity through `ξ`.

For a vertex `x`, `v_ξ(x)` is the first vertex of the ray from `x` toward `ξ`. That ray is an edge path,
since `ξ` is a vertex.

## Theorem

**1. Transport.** Let `x' = v_ξ(x)`. The rule `w ↦ v_ξ(w)` is a bijection from the neighbours `w` of
`x'` in `Lk(x)` with `{x, x', w}` a chamber, to the neighbours `u` of `v_ξ(x')` with `{x', v_ξ(x'), u}` a
chamber. In `Lk(x')` it is the projectivity "unique common neighbour with `v_ξ(x')`".

**2. Chambers at `x` are edges of `T_ξ`.** The map `{v_ξ(x), w} ↦ {π_ξ(x), π_ξ(w)}` is a bijection from
the chambers of `Lk(x)` containing `v_ξ(x)` to the edges of `T_ξ` at `π_ξ(x)`.
- It is compatible with transport.
- It sends the germ of `Q(x, c)`, for `c ∋ ξ`, to the first edge toward the end of `c`.

**3. Classification.** Every `y ∈ Y_Γ` is exactly one of the following:
- `y_o` for a vertex `o`;
- the chamber field `y_c` (`y_c(x)` = the germ of `Q(x, c)`) for a chamber `c` at infinity;
- a wall field `y_(ξ,p)` for a vertex `ξ ∈ ∂Δ` and a vertex `p` of `T_ξ`:
  - `y(x) = v_ξ(x)` if `π_ξ(x) = p`;
  - otherwise `y(x)` is the chamber at `x` that item 2 sends to the first edge of `[π_ξ(x), p]`.

  A pointer toward an end of `T_ξ` instead of a vertex is the chamber field of the corresponding
  chamber.

## Consequences

- **`a2-phase-seed-passes-the-separability-test` becomes unconditional.** Its description (S) is item 3.
- **The wall strata of `a2-lattice-phase-seeds-are-quantum-rigid` are free-group-type pointer shifts on
  panel trees, as conjectured there (What remains, item 1).**
  - The wall labels of one type are exactly the pointer structure of the tree boundary shift, times
    translation along `ξ`.
  - So the tree rigidity argument (monotone chains, as in `free-group-boundary-shift-is-quantum-rigid`)
    is the right tool for each stratum.
  - What remains open for the seed is only the quantum gluing of the strata.

## Lesson for general BH

- **Boundaries of distance-type seeds are horofunction boundaries of polyhedral metrics.** Their strata
  are indexed by faces at infinity: chambers give points, and vertices give panel trees.
- **Classification in a building reduces to apartments.** Two tools do it: a boundary point agrees with
  one genuine field on every finite set, and an edge together with a vertex lies in one apartment.
- **What makes rank 2 tractable.** Uniqueness of common neighbours in the spherical links transports
  chamber germs along rays. That is the same local mechanism as bh-invent-04's Determination Lemma.
- **For other affine types.** They need exactly the analogous uniqueness of short galleries in their
  links (generalized quadrangles and hexagons for `C̃₂` and `G̃₂`).
