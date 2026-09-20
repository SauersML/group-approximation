---
rg: 2
id: star-chains-along-fixed-trees-are-gallery-convex
kind: claim
title: The union of the vertex stars along a geodesic edge path of the CAT(-1) triangle complex of H_31 is convex in the chamber graph (OPEN); hyperbolicity localizes gallery distances near a ray of the fixed tree only to a tube of radius of order 8 delta, which is far too large to compute, and this sharp convexity is the one geometric input needed to turn events (A)/(B) and the one-orbit-per-sector assumption into a finite exact computation; no property-(T) input is needed for it
requires:
  - elliptic-singularity-is-a-marker-mismatch
  - generalized-triangle-group-hosts-reduce-to-fixed-trees
distinct_from:
  elliptic-singularity-is-a-marker-mismatch: that reduces singularity of an elliptic generator to recurrent chamber events (A)/(B); this isolates the geometric lemma that would make those events computable along rays of the fixed tree.
---

**OPEN.** Let `X` be the CAT(−1) triangle complex of `𝓗_31` (CCKW arXiv:2011.09276, Theorem 1.2), `𝒞` its chamber
graph, and `ρ` a geodesic edge path in `X`, for instance a segment of a ray of `Fix(a)`. The claim is:

> **(G)** every geodesic gallery between two chambers of `U_ρ = ⋃_{w ∈ ρ} star(w)` stays in `U_ρ`.

## What is known

- **Trivial case.** At a `C`-type vertex the star is `C_5 × C_5`: 25 chambers `(i, j)`, with link `K_{5,5}`.
  - Gallery distance in the star is 1 if `i = i'` or `j = j'`, and 2 otherwise.
  - Two chambers sharing only the vertex are never adjacent, since adjacency means sharing an edge.
  - So the star is convex.
- **Automatic localization, too large to compute.** `𝒞` is quasi-isometric to `X`, which is hyperbolic. By the Morse
  lemma, geodesic galleries between chambers within distance `r_0` of `ρ` stay within `r_0 + C` of it, with `C`
  depending on `δ(𝒞)` and the quasi-isometry constants.
  - BBMZ locality (`prop:PropertiesSets`(iv)) needs `r_0 ≳ R'(δ)`, of order `8δ + 2`.
  - Every chamber has 12 neighbors, so a tube of that radius has on the order of `11^{8δ}` chambers per step. For any
    `δ(𝒞) ≥ 1` that is beyond `10^{10}`: exact, but out of reach.
- **Why (G) would suffice.** Every ray of `Fix(a)` alternates `A`-type vertices with `B`- or `C`-type ones (Proposition
  4 of `generalized-triangle-group-hosts-reduce-to-fixed-trees`). So `U_ρ` has about `14880 + 625` or
  `14880 + 25` chambers per step.
  - Along a periodic well-sectored ray (`gq-bh-q12-kazhdan-fixed-tree-link-geometry.md`), a few periods give a model
    of order `10^5` chambers.
  - In that model, gallery distances, the atoms `Z_m`, `Y_m`, `E_m` of Proposition H near the ray, and hence events
    (A)/(B), become an exact periodic computation.
  - The same model decides the fiber over the ray's end, and with it the one-orbit-per-sector assumption.
  - That would require (G) for `U_ρ` thickened by the BBMZ window at the front. So the precise statement needed is
    (G) for a bounded thickening of `U_ρ`, with an explicit bound.

## What a proof needs

- **A combinatorial Gauss–Bonnet argument for galleries.**
  - A shortest gallery leaving `U_ρ` and returning bounds, together with a path inside `U_ρ`, a disc diagram in `X`.
  - In that diagram every interior vertex has angle sum at least `2π`. The girths `10, 8, 4` of the links are
    exactly `2π` divided by the angles `π/5, π/4, π/2`, so vertices are flat at their shortest link cycles.
  - The only strict negative curvature is that of the hyperbolic triangles, with defect `π/20` each.
  - The argument must show that the outside detour is never shorter. It must also handle the corners where `ρ` bends,
    where the link distance exceeds the flat value.
- **A model case.** In Euclidean buildings the analogous statement is the convexity of residues (Tits). Its proof
  uses walls, which are absent here. So the building proof does not apply, and a wall-free argument is needed.

## Checks and partial steps (bh-q12-kazhdan, 2026-09-19)

- **Not systolic.** `X` is not 6-large: the link at `C`-type vertices is `K_{5,5}`, of girth 4, and its 4-cycles have
  no diagonals because the link is bipartite. So the Januszkiewicz–Świątkowski convexity theory does not apply.
  Nonpositive curvature here comes from the unequal angles `π/5, π/4, π/2`, not from girth 6.
- **Facts about a single star (proved).** Let `w` be a vertex and `L = L_w`.
  - Two distinct chambers of `star(w)` that are not adjacent share only `w`. If they shared a second vertex `u`, both
    would contain the unique edge `wu`, and so would be adjacent.
  - Inside `star(w)` the adjacency is that of the line graph of `L`, so `d_star(e, e') = min d_L(p, q) + 1` over
    endpoints. Two chambers containing `w` cannot share the edge opposite `w`, since `X` is simplicial.
  - An excursion of a gallery out of `star(w)` leaves and re-enters through outer edges, the edges opposite `w`.
  - At an outer vertex `u`, the chambers of `star(w)` containing `u` are the 5 chambers around the edge `uw`, and they
    are pairwise adjacent. So moving along the outer boundary of `star(w)` costs one step per outer vertex inside the
    star.
- **Lemma G0 (restated after bh-ref-d, 15b37f96f8): star chains without `A`–`B` edges are CAT(0)-convex.** The
  lemma is claimed only for geodesic edge paths `ρ` with no `A`–`B` edge, i.e. rays of `Fix(a)` using only `a`-type
  (`C`–`A`) edges. It is proved there pending the untreated adjacency cases below.
  - **Counterexample to the original version (bh-ref-d).** For an `A`–`B` edge of `ρ`, the apex `u` of a chamber on it
    is `C`-type, with link `K_{5,5}`.
    - For link vertices `c`–`a`–`b`–`d`, with `a = (uw_i)` and `b = (uw_{i+1})`, the in-union path has length `3π/2`.
    - But `c` and `d` are joined by a direct `K_{5,5}` edge of length `π/2` that leaves `U_ρ`.
    - So `U_ρ` is not locally convex at `u`. The two-vertex count below is wrong there: `2π − 3π/2 = π/2 < π`.
  - **Untreated adjacency cases.** An outer vertex adjacent to three vertices of `ρ` occurs at `C`-type vertices of
    `ρ`, where entry and exit are at link distance 2. So do other configurations the referee lists. Until they are
    checked, G0 is a lane claim with a known gap.
  - Let `ρ` be such a geodesic edge path. `U_ρ` is a closed,
  connected subcomplex, and it is locally convex. Hence it is convex in `X` (local-to-global for closed connected
  locally convex subsets of CAT(0) spaces; standard, recalled).
  - At interior points of outer edges, `U_ρ` occupies a half-plane.
  - Let `u` be an outer vertex adjacent to one vertex `w` of `ρ`. The directions at `u` into `U_ρ` form the one-edge
    ball around the link vertex `(uw)` in `L_u`. Two directions at distances `t, t'` from `(uw)` are joined through it by a
    path of length `t + t'`, while any other path has length at least `2π − (t + t')`, because girth times angle is
    `2π`. So this set is `π`-convex. Equality occurs only when `t = t'` is `π/2` at a `C`-type `u`, which is allowed.
  - If `u` is adjacent to two consecutive vertices `w_i, w_{i+1}` of `ρ`, the directions form the union of the
    one-edge balls around two adjacent link vertices. When `ρ` has no `A`–`B` edge, `u` is `B`-type, with edge `π/4`. The same count gives in-union paths of length at most
    `t + ε + t'`, where `ε` is one edge, against at least `2π − (t + ε + t') ≥ 5π/4` for any other path, since the in-union length is at most
    `3π/4`. So the set is again `π`-convex. This fails at `C`-type apexes, which is the counterexample above.
  - This is CAT(0)-convexity. It does **not** give (G): the chamber-graph metric is not the CAT(0) metric, and
    nearest-point projection does not map chambers to chambers.
- **Missing: the curvature count.** A bound on outside excursions by in-star lengths is not proved. It would come
  from Gauss–Bonnet on the reduced disc diagram filling the closed gallery, with flat interior vertices and defect
  `π/20` per triangle. This is not done, even for one `A`- or `B`-type star. So (G) stands as the recorded crux of
  the Kazhdan program.

## Attempt (bh-lemmaG, 2026-09-19): one star proved, strong (G) false, target corrected

Details and proofs in `h31-vertex-stars-are-gallery-convex` (177fa061c6; lane proof, not reviewed).
- **One star (G_star), claimed proved.** Every vertex star is convex in `𝒞` in the strong sense. The proof
  reduces an excursion to its pivot path (an edge path avoiding `v` with at most `k − 2` edges) and proves that
  such paths are at least as long as the link distance (combinatorial Gauss–Bonnet with the angles above and the
  face defect `π/20`; the face term is needed when `v` has type `A` or `B`). Consequence: a geodesic gallery
  between chambers of `U_ρ` never leaves and re-enters the same star.
- **(G) as stated is false** whenever `ρ` has an `A`–`B` edge. At a `C`-type apex `u`, the chambers
  `(u, w_i, x_c)` and `(u, x_d, w_{i+1})` are at distance 2 and are joined by a geodesic gallery through
  `(u, x_d, x_c) ∉ U_ρ` (and by one through `(u, w_i, w_{i+1}) ∈ U_ρ`). This is the gallery form of the `K_{5,5}`
  counterexample to G0.
- **Corrected target.** Either (G_w): `U_ρ` is isometrically embedded in `𝒞`; or (G⁺): the union with the stars
  of the `C`-type apexes of the `A`–`B` edges is strongly convex. Either suffices for the periodic computation.
  A curvature case check (sketch) finds positive inner-side curvature only at those apexes. The open step is
  the junction count between consecutive stars.

## Which inputs are needed

- **No property-(T) input.** (G), events (A)/(B) and the fiber over a ray's end are statements about the local
  geometry of `X`: link girths, angles, and which link vertices the order-5 element fixes. The spectral input that
  gives (T) (the Ershov–Jaikin-Zapirain criterion) plays no role.
- **Where (T) does enter.** Only in the bounded direction: the non-separation of `X` by `Fix(a)` (Niblo–Roller, plus
  cocompactness of the stabilizer, both recalled).

## Lesson for general BH

For wall-free hyperbolic groups, the exact finiteness questions (bounded hosts, singular sets) turn on a gallery
convexity property of star chains along fixed trees. Hyperbolicity alone localizes them, but only at the scale
`8δ`. A sharp combinatorial convexity lemma, which buildings get from walls, is the missing tool.
