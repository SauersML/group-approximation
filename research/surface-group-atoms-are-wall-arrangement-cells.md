---
rg: 2
id: surface-group-atoms-are-wall-arrangement-cells
kind: claim
title: For a closed surface group with the regular 4g-gon side-pairing generators, the atoms of the n-ball are the cells of a finite arrangement of tiling walls, the horofunction boundary has no isolated points, and no cell is a half-plane
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
4. **No cell is a half-plane.** For `n ≥ 1`, every wall `W ∈ 𝒲_n` is crossed by another wall of
   `𝒲_n`. So no cell of `𝒲_n` is an entire half-plane. The cut-vertex branches that drive the
   free-product proof have no analogue here.
   (Correction, 2026-09-18: the first landing stated a gate formula for half-plane cells. It is
   true, but vacuous.)

## What remains for surface groups

The type graph must have a single recurrent component. Item 4 rules out the free-product route
through single-wall gates. Cells near the ideal boundary are bounded by at least two crossing
walls. The natural local pieces are therefore *sector cells*: cells bounded near a tiling vertex
by two consecutive walls through it. Their types and their recurrence are the open step.

## Lesson for general BH

- **Horofunction boundaries of wall metrics are computable.** Whenever the word metric counts
  separating walls, the tree of atoms is the tree of unbounded cells of the growing finite wall
  arrangements. Item 2 uses only this property. Examples: Coxeter groups with Coxeter
  generators, median Cayley graphs, and surface groups with the side-pairing generators.
- **How one-endedness shows up.** Every wall of `𝒲_n` is crossed by another wall of `𝒲_n` at the
  corner of its nearest tile, so no atom is cut off by a single wall. This explains why the
  cut-vertex mechanism behind free products, and the coset gates for amalgams over finite groups
  (bh-free-52), do not transfer directly to one-ended groups.
- **What a one-ended proof needs.** Along this route, a proof of an irreducible core for one-ended
  wall-metric groups has to work with atoms bounded by at least two crossing walls, that is,
  sector cells at vertices where walls cross. No single-wall gate is available.
