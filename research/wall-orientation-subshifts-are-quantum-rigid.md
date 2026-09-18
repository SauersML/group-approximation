---
rg: 2
id: wall-orientation-subshifts-are-quantum-rigid
kind: claim
title: For a group whose Cayley graph carries a wall structure, the subshift of consistent wall orientations (the Roller boundary coded over the group) is quantum rigid (open); true for trees and Z^2, and if true for a non-exact group with walls (Arzhantseva–Osajda type) it refutes (RA′)
requires:
  - quantum-rigid-minimal-topfree-subshift-actions-are-amenable
  - free-group-boundary-shifts-are-quantum-rigid
  - quantum-rigidity-is-product-stable
distinct_from:
  free-group-boundary-shifts-are-quantum-rigid: that is the one-dimensional case, trees, proved by monotone chains; this asks for every wall structure, including infinite-dimensional ones.
  rigid-subshifts-without-isolated-points-factor-onto-the-ends: that turns finite cuts into a boundary map; walls are infinite cuts, so the analogous map lands in the Roller boundary, which for a non-exact group is never amenable.
  quantum-rigid-minimal-topfree-subshift-actions-are-amenable: that is the question (RA); this names the test case that decides its weak form (RA′) at Osajda-type groups.
---

**OPEN.** Posed by lane bh-star-b, 2026-09-18, as the decisive test of (RA′). The calibration cases
are proved below; the rest is not.

## Setting

- `Λ` is finitely generated, with Cayley graph `Cay`. A *wall structure* partitions the edges into
  *walls*. Removing the edges of a wall leaves exactly two components, its *halfspaces*, and each
  site meets finitely many walls. Examples:
  - trees, and every CAT(0) cube complex on which `Λ` acts freely and cocompactly on vertices, with
    walls the dual hyperplanes;
  - `C'(1/6)` graphical small cancellation presentations with walls, as in Wise and in
    Arzhantseva–Osajda (recalled, not re-read).
- **The subshift `R(Λ)`.** Its points are the *consistent orientations*: a choice of halfspace for each
  wall such that any two chosen halfspaces meet, and such that no vertex lies in all of them. The
  second condition removes the principal (vertex) orientations.
  - The symbol at `g` records the chosen side of each wall through an edge at `g`.
  - `R(Λ)` is a closed invariant subset of a finite-alphabet full shift, and it is the Roller boundary
    coded over `Λ`.

## Statement

`R(Λ)` is `D`-quantum rigid for some `D`.

## Proved calibration cases

1. **Trees.** `R(Λ)` is the end shift, which is rigid (`free-group-boundary-shifts-are-quantum-rigid`).
2. **`Z^2` with the square tiling.**
   - The consistent orientations of the vertical walls form the step shift `{x ∈ {0,1}^Z : x
     nondecreasing}`. It is rigid at every scale (row 3 of the calibration in
     `quantum-rigid-subshifts-cluster-the-modifications-of-each-point`), and the same holds for the
     horizontal walls.
   - Vertical and horizontal walls always cross, so consistency does not couple them. Hence
     `R(Z^2) ∪ Z^2` is the product of the two step shifts, which is rigid by
     `quantum-rigidity-is-product-stable`.
   - `R(Z^2)` is a closed invariant subset, rigid by monotonicity.
3. **Products** of wall structures give products of orientation subshifts, so the statement is closed
   under products.

## Why this decides (RA′)

**If the statement holds for a non-exact `Λ`**, then (RA′) is false.
- Take a minimal subset `M ⊆ R(Λ)`. It is rigid by monotonicity, and its action is not amenable,
  because non-exact groups have no amenable actions.
- Whether `M` is topologically free has to be checked. It does hold for trees.
- **Candidates.** Non-exact groups with the Haagerup property, constructed from graphical small
  cancellation over large-girth graphs with walls (Arzhantseva–Osajda; recalled). Osajda's
  residually finite non-exact group is built the same way: its finite stages act geometrically on
  CAT(0) cube complexes (`research/artifacts/exactness-boone-higman-separator-2026-09-17.md`, quoting
  l.396). So the test case sits at Osajda's input itself, up to checking walls in the limit.

**If the statement fails for some wall structure**, the failure is a quantum rigidity obstruction
beyond first order in a setting with no Kazhdan-type rigidity at all. That tells the proof lane where
exactness enters.

## Why "property A from modification clouds" meets this case

- **Trees.** The clouds of a point give exactly property A: the free branches of nested cylinders
  trace the ray to `ξ`, and uniform measures on the first `N` apexes are Reiter functions (via
  `rigid-subshifts-without-isolated-points-factor-onto-the-ends`).
- **Ã₂ (exact, Kazhdan, no walls).** In the rigid boundary skew shift, difference sets contain whole
  apartments through `ω`. The variation sets of cylinders at `g` are cones toward `ω`, and their
  nearest points to `g` form arcs of sectors.
  - Arcs at adjacent sites are bounded translates of each other, so their uniform measures are
    Reiter up to `O(1/R)`.
  - This is a heuristic reading of the building geometry, not a proof from rigidity alone. It
    calibrates the construction: where the action is amenable, the clouds carry the Reiter functions.
- **Wall structures.** In general, sandwiching of cylinders only makes the *depth function*
  `h_x(g, v) = min{R : v ∉ V_R^g(x)}` 1-Lipschitz in `g`. That is wall-counting (Haagerup-type) data,
  not property A.
  - The Arzhantseva–Osajda groups are Haagerup and non-exact. So if the statement holds for them,
    no argument that uses only such data can prove (RA′).

## Lesson for general BH

The two lanes now face one concrete object.
- **Rigidity by compression** worked for trees because walls in a tree are nested chains.
- In a wall structure, crossing walls are independent. For `Z^2`, products handle them.
- The open question is whether consistency of wall orientations still forces commutation when the wall
  structure is **infinite-dimensional and non-exact**.

If it does, the master route's rigid dynamics exist over non-exact groups, and (RA′) is false. If it
does not, the first genuinely higher-order rigidity obstruction appears exactly where property A
fails.

## Progress (bh-star-b, 2026-09-18, later)

- **Proved for finite-dimensional cube complexes** (`roller-compactifications-of-cube-complexes-are-quantum-rigid`).
  The full Roller compactification SFT is rigid at every scale, so all its closed invariant subsets
  are rigid too. The proof uses three properties:
  - walls are locally linked;
  - crossing walls meet;
  - adjacent parallel walls touch.
- **The full compactification fails** when some wall's edges are not uniformly coarsely connected.
  That is the expected case for small-cancellation walls through unboundedly long relators, and there
  finite type fails as well.
- **What remains open for (RA′)** is minimal subsets of such boundaries, where single-wall flips do
  not exist.
