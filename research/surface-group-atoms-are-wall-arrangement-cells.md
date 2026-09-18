---
rg: 2
id: surface-group-atoms-are-wall-arrangement-cells
kind: claim
title: For a closed surface group with the regular 4g-gon side-pairing generators, the atoms of the n-ball are the cells of a finite arrangement of tiling walls, the horofunction boundary has no isolated points, and half-plane cells are gated
distinct_from:
  sft-irreducible-core-iff-unique-recurrent-component: that turns the missing BBMZ hypothesis into a statement about the type graph; this computes the atoms explicitly for surface groups, as geometric input for that statement.
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that is BBMZ-hyperbolic Question 1.1; this settles every hypothesis of the BBMZ theorems for closed surface groups except the irreducible core.
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

**ESTABLISHED** by `surface-group-atoms-wall-cells-proof` (lane `bh-free-23`, lane proof, not
independently reviewed; no priority claimed).

## Setting

- **The group.** `G = π_1(Σ_g)` with `g ≥ 2`, and `S` the `2g` side-pairing generators of the
  regular hyperbolic `4g`-gon `P` together with their inverses. The angles of `P` are `2π/4g`.
- **Walls.** `4g` translates of `P` meet at each vertex of the tiling `G·P`. That number is
  even, so each tiling edge lies on a complete geodesic that is a union of edges: a *wall*.
- **Wall distance.** For a wall `W`, let `D(W)` be the least word length of a tile on the side of
  `W` away from `1`.
- **The arrangements.** Put `𝒲_n = {W : D(W) ≤ n}`. This is a finite set, and `W ∈ 𝒲_n` exactly
  when `W` separates `1` from some element of `B_n`.

## Statement

1. **Distance counts walls.** `Cay(G,S)` is the dual graph of the tiling, and `d(x,y)` is the
   number of walls separating the tiles `x` and `y`.
2. **Atoms are cells.** For every `n`, the atoms for `B_n` (BBMZ arXiv:2309.06224v3,
   `ssec:horofunction`) are the sets `G ∩ R` for `R` a cell of the arrangement `𝒲_n`. The
   infinite atoms are the unbounded cells, and the children of an atom are the unbounded cells
   of `𝒲_{n+1}` inside it.
3. **BBMZ hypotheses.** `∂_h G` has no isolated points, and `G` acts faithfully on it. So, by
   BBMZ `thrm:BBM`, `prop:hyp_similarities` and `thrm:contracting`, the image of `G` in
   `R_{Γ,C_r}` is an RSG isomorphic to `G` with finite nucleus. By
   `sft-irreducible-core-iff-unique-recurrent-component`, it is a contracting RSG exactly when
   the atom-type graph `Γ` has a single recurrent strongly connected component.
4. **Half-plane cells are gated.** Let `n ≥ 1`, and let the cell `R` of `𝒲_n` be an entire open
   half-plane bounded by a wall `W`. Then:
   - `R ∩ B_n` is a single tile `t_0`, adjacent to `W`, with `|t_0| = D(W)`;
   - for every tile `x ⊆ R`, `|x| = |t_0| + d(t_0, x)`.

## What remains for surface groups

The type graph must have a single recurrent component. The natural route mirrors the
free-product proof, with half-plane cells playing the part of the cut-vertex branches:

- (a) every unbounded cell has a half-plane cell among its descendants;
- (b) the type of a half-plane cell is determined by `t_0^{-1}W`, which is one of the `4g` walls
  around the base tile, together with the offset `n − |t_0|`;
- (c) these types reach one another.

Item (b) needs control of the walls that cross `W`: their wall distance `D` can be attained on
the near side of `W`, and that side is where the gate formula of item 4 does not apply.

## Lesson for general BH

- **Horofunction boundaries of wall metrics are computable.** Whenever the word metric counts
  separating walls, the tree of atoms is the tree of unbounded cells of the growing finite wall
  arrangements. Item 2 uses only this property. Examples:
  - Coxeter groups with Coxeter generators;
  - RAAGs and other cubulated groups whose Cayley graph is a median graph with walls as
    hyperplanes;
  - surface groups with the side-pairing generators.
- **Gated half-plane cells replace cut vertices.** They are the one-ended substitute for the
  cut-vertex branches that make free products work
  (`free-products-of-hyperbolic-groups-are-contracting-rsgs`).
- **Where the obstacle lives.** In a median graph every halfspace is gated. So for wall-metric
  groups, the obstruction to the irreducible core, and with it to the BBMZ host for the group
  itself, lives only in the non-median part of the wall geometry. For surface groups that is the
  walls crossing a boundary wall `W` at the tiling vertices.
- **A transferable tool.** This gives a host-construction tool for the whole class of groups with
  wall metrics, and it is not specific to surface groups.
