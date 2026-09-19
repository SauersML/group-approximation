---
rg: 2
id: toms-two-level-spanning-holds-in-every-dimension-proof
kind: route
title: Fills of the components of a closed set that misses faces in two coordinates are laminar and non-separating, so the complement of the maximal fills is one connected set meeting every face; the budget of the level-spanning reduction then gives depth 2
target: toms-two-level-spanning-holds-in-every-dimension
requires: [toms-slice-constant-targets-reduce-to-level-spanning]
---

Write `I^N = [0,1]^N` and `F_nu^0 = {x_nu = 0}`, `F_nu^1 = {x_nu = 1}` for the `2N` faces.
For a set `X`, let `M(X)` be the set of faces that `X` misses, and `G(X)` the union of these
faces.

**Topological facts used.**
- (U) `I^N` is a locally connected, unicoherent continuum. It is contractible, and every
  locally connected contractible continuum is unicoherent (K. Kuratowski, *Topology II*, §57).
- (PB) *Phragmén-Brouwer property.* In a connected, locally connected, unicoherent space: if
  `A` and `B` are disjoint closed sets and neither separates the points `p` and `q`, then
  `A ∪ B` does not separate them (Kuratowski, loc. cit.; see also A. Garcia-Maynez and
  A. Illanes, *A survey on unicoherence and related properties*, An. Inst. Mat. Univ. Nac.
  Autónoma México 29 (1989)). By induction, the same holds for finitely many pairwise
  disjoint closed sets.
- (O) Components of open subsets of `I^N` are open. If `V` is a component of `I^N \ K`, with
  `K` closed and `V ≠ I^N`, then `∅ ≠ ∂V ⊂ K`.
- (F) Faces in two different coordinates intersect. So if `M(X)` contains faces of at least
  two different coordinates, then `G(X)` is connected.

## Part 1: Theorem 1

Let `H` be closed, with no component of `H` face-spanning `N - 1` or more coordinates. Then each
component `K` misses a face in at least two different coordinates, so `G(K)` is connected
by (F). We must find a component of `I^N \ H` that meets all `2N` faces.

**Step 1 (reduction to finitely many components).**
- *A clopen cover.* Let `K` be a component of the compact set `H`, and fix faces `F`, `F'` in
  different coordinates that `K` misses. By the Šura-Bura theorem, `K` is the intersection of
  the clopen subsets of `H` that contain it. These compacta, intersected with `F ∪ F'`, have
  empty intersection, so one clopen `C_K ⊃ K` misses `F ∪ F'`.
- *Disjoint pieces.* Finitely many `C_K` cover `H`. Replacing `C_j` by
  `C_j \ (C_1 ∪ ... ∪ C_(j-1))` gives a partition `H = D_1 ⊔ ... ⊔ D_r` into disjoint compact
  sets. Each `D_j` misses two faces `F_j`, `F'_j` in different coordinates.
- *Thickening.* Choose `eps > 0` below half of every distance `dist(D_j, D_k)` with `j ≠ k`,
  and below every `dist(D_j, F_j ∪ F'_j)`. Let `U_j` be the closed `eps`-neighbourhood of `D_j`
  in `I^N`. The sets `U_j` are pairwise disjoint, and each misses `F_j ∪ F'_j`.
- *Finitely many components.* Let `d_1, ..., d_q` be an `eps/2`-net of `D_j`. The cube is
  convex, so every point of `U_j` is joined inside `U_j`, by a segment, to a point `d` of `D_j`.
  Then `d` is joined to a net point within `eps/2`, inside the ball `B(d, eps) ∩ I^N ⊂ U_j`.
  So `U_j` has at most `q` components.

Hence `H' = ⊔ U_j` is closed and contains `H`. It has finitely many components, and each
misses a face in two different coordinates. If a component of `I^N \ H'` meets all faces,
it lies in a component of `I^N \ H` that meets all faces. So assume `H` has finitely many
components `K_1, ..., K_r`.

**Step 2 (fills).** For a component `K`, let `W_K` be the component of `I^N \ K` that
contains the connected set `G(K)`, and put `fill(K) = I^N \ W_K`.
- By (O), `W_K` is open, so `fill(K)` is closed.
- Its complement `W_K` is connected. So `fill(K)` separates no two points outside it.
- `fill(K)` is `K` together with the components of `I^N \ K` other than `W_K`. None of these
  meets `G(K)`. So `fill(K)` misses every face in `M(K)`.

**Step 3 (fills are laminar).** Let `K ≠ K'` be components of `H`. The connected set `K'`
lies in one component of `I^N \ K`.
- *(a) `K'` lies outside `W_K`.* Then `K' ⊂ fill(K)`, so `K'` misses every face of `M(K)`,
  and `M(K') ⊃ M(K)`. So `G(K') ⊃ G(K)`, and `W_K` meets `W_(K')`. `W_K` is connected and
  disjoint from `K'`, since `K' ∩ W_K = ∅`. Hence `W_K ⊂ W_(K')`, that is
  `fill(K') ⊂ fill(K)`.
- *(b) `K' ⊂ W_K` and `K ⊂ W_(K')`.* We claim `fill(K) ⊂ W_(K')`. It is enough to check each
  component `V ≠ W_K` of `I^N \ K`. Since `V` is connected and disjoint from `K'`, either
  `V ⊂ W_(K')`, or `V` lies in a component `V'` of `I^N \ K'` other than `W_(K')`.

  In the second case, `∂V ⊂ cl V ⊂ cl V' ⊂ V' ∪ K'`, and `V' ∪ K' ⊂ fill(K')` is disjoint
  from `K ⊂ W_(K')`. But `∂V ⊂ K` and `∂V ≠ ∅` by (O). This is a contradiction. So
  `fill(K) ∩ fill(K') = ∅`.
- *(c) `K' ⊂ W_K` and `K ⊄ W_(K')`.* Then (a), with the roles swapped, gives
  `fill(K) ⊂ fill(K')`.

So any two fills are nested or disjoint. Let `P_1, ..., P_s` be the maximal fills. They are
pairwise disjoint, closed, and non-separating. Put `O = P_1 ∪ ... ∪ P_s`. Then
`O ⊃ ∪_j fill(K_j) ⊃ H`.

**Step 4 (the outside is connected).** Let `p, q ∈ I^N \ O`. No `P_i` separates them (Step 2).
By (PB), `O` does not separate them. So `R = I^N \ O` is connected, provided it is non-empty,
which Step 5 shows. Also `R ⊂ I^N \ H`, so `R` lies in a single component `Omega_0` of
`I^N \ H`.

**Step 5 (the outside meets every face).** Fix a face `F`. Suppose `F ⊂ O`. The face `F` is
connected, and the `F ∩ P_i` are disjoint closed sets covering it, so `F ⊂ P_i` for one `i`.
- `P_i` then meets every face except, possibly, the one opposite to `F`.
- But `P_i = fill(K)` misses the faces in `M(K)`, which include faces of two different
  coordinates.

This is a contradiction. So `F` meets `R`, and hence `Omega_0` meets all `2N` faces: it
face-spans every coordinate.

**The level-set form.** Let `max delta <= 1`, and put `H = {delta = 1} = {delta >= 1}`, which is
closed. The level-0 components are the components of `I^N \ H`, and the level-1 components
are the components of `H`.
- If some level-1 component face-spans `N - 1` coordinates, it fails to span at most
  `1 = delta` coordinates.
- Otherwise, Steps 1-5 give a level-0 component that spans all `N`, and it fails `0`.

Face-spanning implies spanning (the face `x_nu = 0` lies in `A`, and `x_nu = 1` in `C`). So (S)
holds whenever `max delta <= 1`. (For `N = 1` it is trivial.) ∎

## Part 2: depth 2

Write `c_nu(X)` for the number of open chambers that `pi_nu X` meets, and `c(X) = sum_nu c_nu(X)`.
Closure adds only endpoints of `pi_nu X`, so `c_nu(cl X) = c_nu(X)`. The definition of `e` in
`toms-slice-constant-targets-reduce-to-level-spanning` then reads
`E(cl Omega) = c(Omega) - N`. The wall-point case matches: there `e = -1 = 0 - 1`.

Suppose the budget `delta(Omega) + E(cl Omega) <= beta` holds for every level component, and
that `max delta <= 1`. Part 1 gives one of the following.
- *A level-0 component spanning all `N` coordinates.* Then `E = 2N`, so `2N <= beta`.
- *A level-1 component spanning at least `N - 1` coordinates.* The spanned coordinates have
  `e = 2` and the others have `e >= -1`. So `E >= 2(N - 1) - 1` and `1 + 2N - 3 <= beta`, that
  is `beta >= 2N - 2`.

Hence:
- `beta <= 2N - 3` forces `max delta >= 2`;
- `beta <= 2N - 1` forces `max delta >= 1`, because `delta = 0` makes the cube one component
  with `E = 2N`.

Part 1 of `toms-slice-constant-targets-reduce-to-level-spanning` gives `beta = N` for
slice-constant targets, and the depth is at least `max delta`. So the depth is at least `2`
for every `N >= 3`. ∎

## Part 3: the cases where the bound is now exact

The target bound is `max delta >= N - floor(beta/2)`.
- For `beta >= 2N - 4` its right side is at most `2`.
- Part 2 gives `max delta >= 2` for `2N - 4 <= beta <= 2N - 3`, and `max delta >= 1` for
  `2N - 2 <= beta <= 2N - 1`.
- The bound is vacuous at `beta = 2N`.

With `beta = N`, the condition `beta >= 2N - 4` means `N <= 4`. So slice-constant targets have
depth at least `ceil(N/2)` for `N = 3, 4`. This is sharp by Theorem part 3 of
`toms-slice-constant-targets-reduce-to-level-spanning` (staggered targets). ∎

## Part 4: where the two level inductions die

(S) itself, for general `delta`, is equivalent to its face-spanning form only in one
direction. The inductions below are the natural ways to lift Part 1. Each needs a relative
lemma, and each relative lemma is false.

**Top-down.**
- *The step.* Assume no level-0 component spans all `N`. Part 1, applied to `H = {delta >= 1}`
  with face-spanning, gives a component `Y` of `{delta >= 1}` face-spanning at least `N - 1`
  coordinates.
- *What finishing needs.* Level components of `delta` at levels `t >= 1` lie in components of
  `{delta >= 1}`. To finish by induction, one would need Part 1 relative to a continuum:

  > (L*) If a continuum `Y` face-spans a set `S` of `s` coordinates, and `G ⊂ Y` is closed
  > with every component face-spanning at most `s - 2` coordinates, then some component of
  > `Y \ G` face-spans all of `S`.

  Part 1 is (L*) for `Y = I^N`.
- *(L*) is false.* Let `Y` be the boundary of the square `[0,1]^2 x {z}` (with `z` fixed in
  the other coordinates), and `G` its two corners `(0,0)` and `(1,1)`.
  - `Y` face-spans `x_1` and `x_2`, so `s = 2`.
  - Each corner face-spans nothing.
  - Each of the two open arcs of `Y \ G`, for instance `{(x,0) : 0 < x <= 1} ∪ {(1,y) : 0 <= y < 1}`,
    meets only the faces `x_2 = 0` and `x_1 = 1`. So it face-spans nothing.
- *Where it dies.* The proof of Part 1 uses unicoherence of the ambient space in (PB). A
  component of `{delta >= 1}` need not be unicoherent. Any proof of (S) for `max delta >= 2`
  must use the badness of the lower levels together with the geometry of the cube, and not
  only the continuum `Y`.

**Bottom-up.**
- *The weighted form.* Let (B) say that some level component has
  `c(Omega) + delta(Omega) >= 3N - 2 max delta`. By the identity in Part 2, (B) for all `delta`
  is equivalent to the bound `max delta >= N - floor(beta/2)` for every budget `beta`.
- *The reduction.* Put `T = max delta` and `delta'' = max(delta - 1, 0)`, which is usc with
  maximum `T - 1`. Induction gives a `delta''`-level component `Omega''` with
  `c + t'' >= 3N - 2T + 2`.
  - If `t'' >= 1`, then `Omega''` is a `delta`-level component at level `t'' + 1`, and it has
    slack `3`.
  - If `t'' = 0`, then `Omega''` is a component `Z` of `{delta <= 1}`, open and connected, with
    `c(Z) >= 3N - 2T + 2`. What is needed is:

  > (R) If `Z` is open and connected and `g : Z -> {0,1}` is usc, then some level component
  > `P` of `g` has `c(P) + g(P) >= c(Z) - 2`.

  (R) implies (B) for all `T`, and (R) for `Z = I^N` is (B) at `T = 1`.
- *(R) is false.* Let `gamma` be the path from `(0,0)` to `(1,0)` to `(1,1)` in coordinates 1 and 2,
  with the other coordinates fixed at interior points of chambers. Let `Z` be its open
  `rho`-neighbourhood, with `rho` below every wall distance involved.
  - Then `c(Z) = 3 + 3 + (N - 2) = N + 4`.
  - Put `g = 1` on the four cross-sections `Z ∩ {x_1 = w_1}`, `Z ∩ {x_1 = w_2}` (on the first
    leg) and `Z ∩ {x_2 = w_1}`, `Z ∩ {x_2 = w_2}` (on the second leg), and `g = 0` elsewhere.
  - Each cross-section has `c = 0 + 1 + (N - 2)` and `g = 1`.
  - Each of the five level-0 pieces lies in one chamber in every coordinate, so `c = N`.

  All pieces have `c + g = N < N + 2`.
- *Where it dies.* A thin `Z` is one-dimensional, and cutting it costs 2 per spanned
  coordinate. The loss is paid back at the higher level: with `delta = 2` off `Z`, the
  component `I^N \ Z` satisfies (B). So the reduction is lossy, and (B) is not refuted.
  Any bottom-up proof must price the thinness of `Z` against the levels outside it.

## Part 5: search evidence

`anneal.c` performs simulated annealing over usc functions on the product cell complex, with
`6m + 1` cells per coordinate. Components are joined along faces of equal level. The score
counts, over all components, how far each is from satisfying (S), (T) (`3t + c >= 3N`) or (B).
A score of `0` would be a counterexample.
- `N = 3`, `m = 1`: best score `1` in all three modes.
- `N = 3`, `m = 2`, `max delta <= 2`: best `1` for (S) and (T), two seeds each, `1.5 x 10^6`
  steps.
- `N = 4`, `m = 1`, `max delta <= 1`: best `1` for (B), three seeds.

`results.json` records the runs. This is evidence only. Part 1 proves the `max delta <= 1` cases.
