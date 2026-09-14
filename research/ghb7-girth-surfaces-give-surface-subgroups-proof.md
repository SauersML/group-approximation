---
rg: 2
id: ghb7-girth-surfaces-give-surface-subgroups-proof
kind: route
title: Girth link walks make the developing map a local isometric embedding into the CAT(-1) complex of GHB_2(7)
target: ghb7-girth-surfaces-give-surface-subgroups
requires: [cckw-ghb2-kms-group-structure]
artifacts:
  - research/artifacts/ideas-growth-hyperbolic-2026-09-14.md
  - experiments/ghb7-girth-surfaces/intersections.py
---

The notation is that of the target. BH is Bridson–Haefliger (1999), read at source.

## Step 1. Local structure of `Y`

By CCKW Theorem 3.1(i),(v) (items 2–3 of `cckw-ghb2-kms-group-structure`), `G` acts by
simplicial isometries on a CAT(−1) simplicial complex `Y`.
- A chamber `C = (v_0, v_1, v_2)` is a strict fundamental domain.
- `C` is a hyperbolic triangle with angle `π/r_i` at `v_i`, where `r_i` is half the girth of the
  coset graph of `X_i`.
- `Stab(v_i) = X_i`.

The girths are 6, 8, 8 (`cckwLinkGirths`, and recomputed in
`experiments/ghb7-girth-surfaces/search-t24.log`), so the angles are `π/3, π/4, π/4`.

`experiments/ghb7-girth-surfaces/intersections.py` computes in `SL_4(F_7)` that
`ψX_i ∩ ψX_j = ψ<g_k>` whenever `{i,j,k} = {0,1,2}`, and that `ψX_0 ∩ ψX_1 ∩ ψX_2 = 1`. Since `ψ`
is injective on each `X_i`, the same holds in `G`: `X_i ∩ X_j = <g_k>` and `X_0 ∩ X_1 ∩ X_2 = 1`.

(a) *Every simplex of `Y` is `gF` for a face `F` of `C`.* Let `y` be an interior point of a
simplex `σ`, and write `y = g y_0` with `y_0 ∈ C`. Then `y_0` is interior to `g^{-1}σ` and lies in
`C`, so `g^{-1}σ` is a face of `C`.

(b) *Stabilizers.* The vertices of `C` lie in distinct orbits. So if `gC = C`, then `g` fixes every
vertex of `C` and `g ∈ X_0 ∩ X_1 ∩ X_2 = 1`, and `G` acts simply transitively on chambers.
Similarly `Stab(e_k) = X_i ∩ X_j = <g_k>`.

(c) *Simplices at a vertex.* Suppose `gσ ∋ v_i` for a face `σ` of `C`. Then `g^{-1}v_i` is a vertex
of `σ` in the orbit of `v_i`, so `g ∈ X_i`. So the chambers at `v_i` are the `xC` with `x ∈ X_i`,
all distinct. The edges at `v_i` are the `x e_j` and `x e_k`, and `x e_j = x' e_j` if and only if
`x^{-1}x' ∈ <g_j>`.

So the geometric link `Lk(v_i, Y)` is the metric graph `Γ_i`:
- its vertex set is `X_i/<g_j> ⊔ X_i/<g_k>`;
- it has one edge of length `π/m_i` for each `x ∈ X_i`, joining `x<g_j>` to `x<g_k>`;
- its combinatorial girth is `2m_i`.

In the same way, the chambers containing `e_k` are the `hC` with `h ∈ <g_k>`.

## Step 2. The surface

`S` is an `M_{−1}`-polyhedral complex in the sense of BH Definition I.7.37: every `r_k` is
fixed-point-free, and faces are identified only by the identity maps of sides.
- An interior point of a side has two half-discs around it.
- The corners identified with the `v_i`-corner of `Δ_t` are indexed by the `<r_j, r_k>`-orbit of
  `t`. That orbit has exactly `2m_i` points, arranged cyclically by alternating `r_j` and `r_k`. So
  the vertex has a disc neighbourhood of total angle `2m_i · π/m_i = 2π`.

Hence `S` is a closed surface, connected by transitivity, and every link is a circle of length `2π`.
It has `V = T/6 + T/8 + T/8` vertices, `E = 3T/2` edges and `F = T` faces, so `χ(S) = −T/12`.

Let `S̃` be the universal cover, with the lifted polyhedral structure.
- `Shapes(S̃)` is one triangle, so `S̃` is a complete geodesic space (BH Theorem I.7.50).
- For every `w ∈ S̃`, the quantity `ε(w)` of BH 7.38 is positive: `w` lies in finitely many cells,
  and in each of them the point over `w` has positive distance to the faces not containing it.

## Step 3. The developing map

Every chamber `D` of `S̃` lies over some `Δ_t`. Crossing from `D` across its side of type `k` carries
the element `g_k^{x(t,k)}`. For a gallery `γ`, let `h(γ)` be the product of its crossing elements.

*`h(γ)` depends only on the endpoints of `γ`.* The dual cell complex of the triangulation (one
0-cell per chamber, one 1-cell per side, one 2-cell per vertex) is a cell structure on the simply
connected surface `S̃`. So two galleries with the same endpoints differ by two kinds of moves.
- Inserting or deleting a backtrack contributes `g^x g^{−x} = 1`.
- Inserting a full turn around a vertex contributes a cyclic rotation of a vertex word, or of its
  inverse, which is 1 by the vertex condition.

Fix a base chamber `D_0`. For a chamber `D`, pick a gallery `γ` from `D_0` to `D`, and let `F` map
`D` onto `h(γ)C` by the type-preserving isometry.
- *Consistency.* If `D'` is adjacent to `D` across type `k` with crossing `g_k^x`, then
  `h(γ') = h(γ) g_k^x`. Since `g_k` fixes `e_k` pointwise, the two maps agree on the common side.
- So `F : S̃ → Y` is continuous, and it is an isometry on each chamber.
- Deck transformations preserve crossing labels. So `F(σD) = φ(σ) F(D)`, where `φ(σ) = h(D_0 → σD_0)`
  is a homomorphism `π_1(S) → G`.

## Step 4. Link maps preserve `d_π = min(d, π)`

**At a vertex `w` of type `i`.** Translate so that `F(w) = v_i`.
- The chambers around `w` map, in cyclic order, to `c_0C, …, c_{2m_i−1}C`, with
  `c_{p+1} = c_p g_{k_p}^{±x_p}` and every `x_p ≢ 0`.
- In `Γ_i` this is a closed walk of `2m_i` edges, of length `2π`. It has no backtracking, because
  `c_{p+1} ≠ c_p`.

*The walk is an embedded cycle `Z`.* If a vertex repeated, the walk would split off a shorter
closed walk with no interior backtracking. That walk carries a nontrivial cycle shorter than the
girth.

*`Z` is isometric for `d_π`.* Suppose `u, u' ∈ Z` have `d_{Γ_i}(u,u') < d_Z(u,u') ≤ π`.
- Subdivide at `u` and `u'`. Let `σ` be a geodesic from `u` to `u'` in `Γ_i`, and `α` the shorter
  arc of `Z` between them.
- `σ` and `α` are distinct reduced paths, because `σ` is shorter. So the loop `σα^{-1}` does not
  reduce to a point.
- Its cyclic reduction is a nontrivial cycle of length `< 2π`, which contradicts the girth.

**At an interior point of a side.** The link of `S̃` is two semicircles. They map to two distinct
arcs of the seven arcs at `F(w)`, distinct because `x ≢ 0`. Two arcs form an isometrically embedded
circle.

**At an interior point of a chamber.** There is nothing to check.

## Step 5. `F` is locally an isometric embedding

By BH Theorem I.7.39, small balls about `w ∈ S̃` and about `F(w) ∈ Y` are isometric to balls about
the cone points of the `(−1)`-cones over the links.
- `F` is isometric on chambers, so it sends the point at distance `t` in direction `u` to the point
  at distance `t` in direction `f(u)`, where `f` is the link map. So `F` is the cone over `f`.
- The cone metric depends only on `d_π` of the link (BH Definition I.5.6), and `f` preserves `d_π`
  by Step 4.
- So `F` restricted to a small ball is an isometry onto its image.

## Step 6. `F` is an isometric embedding

Let `c` be a geodesic in `S̃` from `p` to `q` (Step 2). By Step 5, `F∘c` is a local geodesic in `Y`.
`Y` is CAT(−1), so `F∘c` is a geodesic (BH Proposition II.1.4(2), with `D_κ = ∞`). Hence
`d_Y(F p, F q) = d(p,q)`.

## Step 7. Conclusion

*Injectivity.* Suppose `φ(σ) = 1`. Then `F(σD_0) = F(D_0)`, so `σD_0 = D_0` because `F` is injective.
Deck transformations act freely, so `σ = 1`.

*Quasiconvexity.* Put `H = φ(π_1 S)` and `x_0 = F(w_0)` for a point `w_0 ∈ D_0`.
- `F(S̃)` is convex. Geodesics in `Y` are unique (BH Proposition II.1.4(1)), and by Step 6 `F` sends
  the geodesic between two points of `S̃` to a geodesic between their images.
- `F(S̃)` lies in the `D`-neighbourhood of `H·x_0`, where `D` is the diameter of the compact
  surface `S`, because `F(σx) = φ(σ)F(x)`.
- `G` acts by isometries on the length space `Y`, properly (finite stabilizers, locally finite
  complex) and cocompactly (compact fundamental domain `C`). By the Švarc–Milnor lemma
  (BH Proposition I.8.19), `g ↦ g·x_0` is a quasi-isometry from `G`, with a word metric, to `Y`.
- `G` is hyperbolic (item 1 of `cckw-ghb2-kms-group-structure`). A quasi-inverse `Y → Cay(G)` is a
  quasi-isometric embedding of geodesic spaces, so `Y` is hyperbolic (BH Theorem III.H.1.9).

Let `h, h' ∈ H`, and let `γ` be a geodesic in the Cayley graph from `h` to `h'`.
1. The orbit map sends `γ` to a `(λ,ε)`-quasi-geodesic. By BH Theorem III.H.1.7, it lies within
   Hausdorff distance `R` of `[h x_0, h' x_0]`.
2. That geodesic lies in `F(S̃)`, hence within `D` of `H·x_0`.
3. So every vertex `g` of `γ` has some `h'' ∈ H` with `d_Y(g x_0, h'' x_0) ≤ R + D`. The orbit map is
   a quasi-isometry, so `d_G(g, h'')` is bounded independently of `h` and `h'`.

This proves that `H` is quasiconvex in `G`.

*Genus.* `π_1(S)` is a closed surface group with `χ = −T/12 < 0`. If `S` is orientable, its genus
is `1 + T/24`. A connected double cover, orientable in either case, gives genus `1 + T/12`.
