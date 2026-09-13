# Zaremsky Problem 4.2: bounded computational search, part 1 (2026-09-13)

Lane z4-02-planar-rips. Question: is every connected Rips complex of a (finite) planar set homotopy
equivalent to a wedge of spheres? Root: `zaremsky-4-02-planar-rips-complexes-wedges-of-spheres`.

This is evidence, not proof. It records what was searched, how, and what came out, so later attacks
can avoid repeating it. Runs used at most 8 cores on sioux, each for a few minutes.

## Method

For a finite `X ⊆ R^2` and scale `r`, build the unit-distance graph (pairs at distance `≤ r`), split
it into components, and reduce each component by
- deleting dominated vertices (`N[v] ⊆ N[u]` for a neighbour `u`), and
- deleting dominated edges (`N[u] ∩ N[v] ⊆ N[w]` for a common neighbour `w`; Boissonnat–Pritam edge
  collapse).

Both deletions preserve the homotopy type of the clique complex. On the reduced core, enumerate all
cliques and compute boundary ranks mod 2, mod 3 and mod `P = 1000003`. Two certificates of
non-wedge type were tested:

- **Torsion (T):** Betti numbers mod 2 or mod 3 differ from those mod `P`.
- **Winding (W):** pick a point `p` outside the shadow of the core; build the chain complex of the
  infinite cyclic cover pulled back from the angle around `p`, with coefficients `±λ^{c}`; compare
  Betti numbers at a random `λ` with the ordinary ones. By
  `wedges-of-spheres-have-free-cyclic-cover-homology`, a wedge has `b_q(λ) = b_q(1)` for `q ≥ 2` and
  `b_1(λ) = b_1(1) − 1`.

Scales were midpoints between consecutive distinct pairwise distances, or random values in a stated
range.

**Calibration (model tests), all as expected:**
- regular hexagon, `r = 1.9`: `b = [1,0,1]`, the octahedron;
- regular octagon, `r` just above the step-3 chord: `[1,0,0,1]`, `S^3`;
- regular 9-gon at the critical step-3 scale: `[1,0,2]`, `S^2 ∨ S^2` (Adamaszek's critical case);
- 12-gon at small scale with hole at the centre: `b = [1,1]`, twisted `m = [0,0]`, no flag;
- abstract 6-vertex `RP^2`: mod-2 Betti `[1,1,1]` versus mod-`P` `[1,0,0]`, so torsion is flagged.

## Families and counts (complexes with a reduced core of at least 4 vertices)

| family | description | complexes | holes tested | T | W |
|---|---|---|---|---|---|
| disk | 7–13 uniform points in a disk, 30 scales | 537 | 532 | 0 | 0 |
| ring | 2–4 concentric circles, 12–24 points each, random offsets | 3242 | 3115 | 0 | 0 |
| clusters | 5–10 hexagons/octagons around a ring, fixed/rotating/random | 1736 | 1697 | 0 | 0 |
| lattice | triangular-lattice annuli with 20% deletions | 1395 | 1293 | 0 | 0 |
| hexring | up to 48 translated or slowly rotated hexagons around a ring | 2028 | 1995 | 0 | 0 |
| octring | same with octagons | 1206 | 1206 | 0 | 0 |
| decring | same with decagons | 729 | 729 | 0 | 0 |
| annulus | 25–70 random points in an annulus | 899 | 633 | 0 | 0 |
| twocircle | two concentric polygons, all critical scales | 4632 | 3873 | 0 | 0 |
| tracks | 3–6 dotted concentric circles within a band `< r` | 275 | 275 | 0 | 0 |
| squash | rings of squashed hexagons/octagons | 786 | 786 | 0 | 0 |
| nearcircle | 8–22 noisy points near a circle, `r ∈ [1.4, 2.1]` | 2614 | – | 0 | – |
| reuleaux | noisy points on Reuleaux 3/5/7-gons near their width | 1999 | – | 0 | – |
| multi | 2–3 noisy concentric circles near the diameter | 2232 | – | 0 | – |

No certificate fired, so no torsion and no winding violation was found in about 24,000 complexes.

## Observations worth keeping

1. **Sliding kills local spheres.** Every `tracks` and `squash` complex reduced to `S^1` (`b = [1,1]`,
   `m = [0,0]`). A crosspolytope sphere carried along dense parallel tracks does not survive
   collapse. The rings of separated clusters gave wedges `S^1 ∨ ⋁ S^2` (for example `b = [1,1,14]`,
   `m = [0,0,14]`), with independent local spheres.
2. **Near-diameter cores are almost always cycles and matchings.** For cores at scales near the
   diameter, the far graph (pairs at distance `> r`) on the core vertices had these degree
   signatures:
   - `S^2` cores: 666, nearly all perfect matchings on 6 vertices (octahedra), plus 10 on 7 vertices
     with degrees `[1,1,1,1,2,2,2]`;
   - `S^2 ∨ S^2` cores: 91, almost all 2-regular on 9 vertices (the cycle `C_9`, whose independence
     complex is `S^2 ∨ S^2`);
   - `S^3` cores: 48, perfect matchings on 8 vertices, plus one 2-regular graph on 11 vertices
     (`C_11`);
   - `S^4`: 5, matchings on 10 vertices;
   - `S^2 ∨ S^2 ∨ S^2`: 2, cubic far graphs on 12 vertices.

   When the far graph is a disjoint union of cycles and edges, the Rips complex (the independence
   complex of the far graph) is a join of spheres and of wedges of two spheres, hence a wedge. The
   rare cubic cores are the next thing to inspect.

## Next

- Dump and classify every core whose far graph is not a disjoint union of cycles and edges (degree
  `≥ 3` or mixed degrees), including the cubic 12-vertex cores.
- Look for a structure theorem for cores of planar Rips complexes at any scale; a positive answer to
  Problem 4.2 could go through one.
