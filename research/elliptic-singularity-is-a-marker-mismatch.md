---
rg: 2
id: elliptic-singularity-is-a-marker-mismatch
kind: claim
title: For a finite-order element g whose nontrivial powers are generators, the atoms of the neighborhoods of the orbit <g> form a g-invariant chain that interleaves both the atoms of the balls around 1 and their g-translates, and g is singular at a point exactly when the two markers in these intervals disagree infinitely often; a fixed tree with Cantor boundary can carry continuum many singular points, so a bounded host for a Kazhdan group needs more than the shape of its fixed trees
requires:
  - bbmz-singularity-is-a-recurrent-coincidence
  - racg-generators-are-singular-over-their-wall-trees
  - generalized-triangle-group-hosts-reduce-to-fixed-trees
distinct_from:
  bbmz-singularity-is-a-recurrent-coincidence: that proves the sandwich and the RACG coincidence criterion; this gives a criterion for elliptic generators in any hyperbolic group, built from the orbit of the generator instead of walls.
  generalized-triangle-group-hosts-reduce-to-fixed-trees: that reduces H_31 to its generators and computes their fixed trees; this replaces the two sides of a wall by the orbit and records that fixed-tree shape alone cannot decide boundedness.
---

**Status.**
- **ESTABLISHED** (lane proof, bh-q12-kazhdan, 2026-09-19; not reviewed): Proposition H and Remark I.
- **OPEN:** the application to `𝓗_31`, the sector events below.
- No computation was run, and no priority is claimed.

## Setting

- `G` is hyperbolic with finite symmetric generating set `S`. Let `g` have finite order with every nontrivial power
  in `S`, and put `F = ⟨g⟩`.
  - Example: the edge-group generators of a generalized triangle group, whose Cayley graph is the chamber graph.
  - In a right-angled Coxeter group, standard generators qualify, with `F = {1, s}`.
- `N_m = ⋃_{h ∈ F} hB_m`, the `m`-neighborhood of `F`. Every `h ∈ F` is within distance 1 of `1`, so
  `hB_m ⊆ N_m ⊆ hB_{m+1}` for every `h ∈ F`, including `h = 1`.
- **Three families of shadows around a point `p`.** In each case the shadow is that of the atom containing `p`:
  - `Y_m(p)` for atoms of `N_m`;
  - `Z_m(p)` for atoms of `B_m`;
  - `E_m(p) = g Z_m(g^{-1}p)` for atoms of `gB_m`.

## Proposition H (orbit atoms and marker mismatch)

1. **Invariance.** `g Y_m(p) = Y_m(gp)` for all `m` and `p`.
2. **Interleaving.** Put `I_m(p) = [Y_m(p), Y_{m−1}(p)]`, the sets between the two endpoints. Then:
   - `Y_{m−1}(p) ⊇ Z_m(p) ⊇ Y_m(p)`;
   - `Y_{m−1}(p) ⊇ E_m(p) ⊇ Y_m(p)`.

   So each interval carries one **Z-marker**, `Z_m(p)`, and one **E-marker**, `E_m(p)`.
3. **Criterion.** `g` is regular at `y` iff, for all large `m`, the E-marker of `I_m(gy)` equals its Z-marker, or
   equals an endpoint of `I_m(gy)` that is the Z-marker of the neighboring interval.

   So `g` is singular at `y` iff these markers mismatch for infinitely many `m`.

*Proof.*
1. `gN_m = N_m`, and left multiplication is an isometry. So `x, x'` agree modulo constants on `N_m` iff `gx, gx'`
   agree on `gN_m = N_m`.
2. Atoms of a larger set are finer, so `B_m ⊆ N_m ⊆ B_{m+1}` gives `Z_{m+1} ⊆ Y_m ⊆ Z_m`. Apply `g` to the same
   inclusions at `g^{-1}p` and use part 1.
3. By definition, `g` is regular at `y` iff `E_m(gy)` is a Z-shadow around `gy` for all large `m`.
   - The intervals `I_m` are nested, and consecutive ones share only an endpoint.
   - `Z_k(gy)` lies in `I_k(gy)`. So `E_m(gy) = Z_k(gy)` forces either `k = m`, or `k = m ± 1` with `E_m(gy)` the
     common endpoint. ∎

**Calibration (sketch; it uses the wall-cylinder description of `N_m`-atoms, as in Theorem D, step 1).** In a right-angled Coxeter group with `g = s`:
- on the `1`-side, `Y_m(σ_+) = Z_m(σ_+)`, because (+)-walls and crossing walls are no closer to `s` than to `1`;
- on the far side, `Y_m(σ_−)` is the cylinder of the (−)-walls of depth `≤ m + 1` and the crossing walls of depth
  `≤ m`. So the transported marker `Y_m(σ_−) = sZ_m(σ_+)` is a Z-shadow unless both kinds of wall cut at depth
  `m + 1`.

This recovers Theorem D.

## Remark I (fixed-tree shape does not decide boundedness)

In the Petersen-graph right-angled Coxeter group, `Fix(s) = H_s` is a tree with Cantor boundary. By
`racg-generators-are-singular-over-their-wall-trees`, `s` is singular at continuum many points over it.
- So the statement "a fixed tree with Cantor boundary carries no singular points" is false in general.
- A proof that the host of `𝓗_31` is bounded, the surprising direction, must use something beyond the trees of
  Proposition 4 of `generalized-triangle-group-hosts-reduce-to-fixed-trees`. The natural candidate is the
  (T)-specific input that `Fix(a)` does not coarsely separate the complex.

## The sector events for 𝓗_31 (OPEN; heuristic picture)

- **The expected picture.** Let `ζ ∈ ∂Fix(a)` be generic. The fiber over `ζ` should contain an `a`-orbit
  `σ_0, …, σ_4`, one for each local sector around the ray of `Fix(a)`, with `σ_0` on the side of the base chamber
  `T`. This is not proved.
  - The offsets are then `+1, −1, 0, 0, 0`, since `Σ_j ℓ_a(a^j σ) = 0` by telescoping. So `ζ ∈ F'_a`.
- **The criterion in this picture.** If `Y_m(σ_0) = Z_m(σ_0)` (the Coxeter behavior on the base side), then by
  Proposition H, `a` is singular at `σ_0` iff `Y_m(σ_1)` lies strictly between `Z_m(σ_1)` and `Z_{m+1}(σ_1)` for
  infinitely many `m`. That means two events recur together:
  - **(A)** a chamber at distance `m + 1` from `T` but `≤ m` from some `a^jT` (`j ≠ 0`) separates points of
    `Z_m(σ_1)`;
  - **(B)** a chamber at distance `m + 1` from every `a^jT` separates points of `Y_m(σ_1)`.
- **Relation to the Coxeter case.** These events play the roles of the crossing walls and the (−)-walls. Deciding
  whether they recur together along rays of `Fix(a)` is a local computation in the vertex links met by the ray.
  - At an `A`-type vertex, the element of order 5 fixes the entry and exit link vertices.
  - It permutes the link geodesics between them in orbits of 5, since no link edge is fixed.
  - The number of such orbits decides whether sectors propagate bijectively (one orbit) or merge (several).

## Lesson for general BH

- **Replace the two sides of a wall by the orbit.** For an elliptic generator, the neighborhoods of its orbit give a
  `g`-invariant atom chain.
- **Singularity is a marker mismatch.** It happens when the ball atoms around `1` and their `g`-translates sit
  differently inside that chain, infinitely often.
- **What decides it.** Walls make the mismatch automatic. Without walls, it is decided by how sectors around the
  fixed tree propagate through vertex links.
