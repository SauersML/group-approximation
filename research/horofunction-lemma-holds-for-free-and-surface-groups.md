---
rg: 2
id: horofunction-lemma-holds-for-free-and-surface-groups
kind: claim
title: For free groups (free basis) and closed surface groups (standard generators), every R-locally distance-like gradient field is a limit of distance functions, so the distance-gradient SFT is an SFT compactification with dense seed orbit
---

**ESTABLISHED** (lane proof, bh-invent-13, 2026-09-18; elementary; not reviewed).

**Setting.** This is part 4 of `finite-type-branch-blow-ups-are-sft-compactifications` (the parent):
`Y_R` is the SFT of gradient fields of functions `f : S → Z` whose restriction to every ball `B_R(v)` is, up
to a constant, that of some `d(·,q)`. (HL) says that every `f ∈ Y_R` lies in `K_h = \overline{S·∇d(·,1)}`.

## Theorem

1. `S = F_n` (`n ≥ 2`), free basis, any `R ≥ 1`: (HL) holds.
2. `S = Γ_g` (`g ≥ 2`), generators `a_1, b_1, …, a_g, b_g` of `∏[a_i,b_i]`, `R ≥ R_0(g)`: (HL) holds.

With part 4(a) of the parent (take also `R ≥ k(δ)+2`), `(Y_R, ∇d(·,1)|_{B_R})` is an SFT compactification in both
cases, and (IE′) holds for `F_n` and for the one-ended groups `Γ_g`.

## Proof of 1 (trees)

- Gradients are `±1`: an orientation of each edge, pointing down. On a 1-ball, a distance pattern has at most one
  descending edge. So every vertex has out-degree `≤ 1`. If some vertex `v` has out-degree 0, induction outward from `v` gives `f = d(·,v) + c`. Otherwise every vertex has out-degree exactly 1.
- Any two forward paths merge: on the geodesic between their starts no vertex has two outgoing path edges.
- Let `γ` be the descending ray from `1`, let `h` be any vertex, and let the descending ray from `h` meet `γ` at `w`.
  - Then `f(h) − f(1) = d(h,w) − d(1,w)`.
  - For `γ_m` beyond `w`, `d(h,γ_m) − m = d(h,w) − d(1,w)`.
  - So `f − f(1) = b_γ`, and the parent's 4(b) gives `f ∈ K_h`. ∎

## Proof of 2 (walls)

**The walls.**
- The Cayley graph is the 1-skeleton of the tiling of `H²` by regular `4g`-gons, `4g` at a vertex. The dual tiling
  is the same, and its tiles `P_v` have angles `π/(2g)`, so they are Coxeter polygons.
- The Cayley graph is therefore the chamber graph of the reflection group of `P_v`, and
  `d(x,y) = #{walls separating x, y}`, where the walls are the lines carrying dual edges (chamber distance in a
  Coxeter complex).
- Each edge crosses one wall.
- Two walls meet only at dual vertices `p`, i.e. at centres of Cayley faces. Through each `p` pass `2g` walls,
  dual to the `4g` face edges.
- Distinct walls are never asymptotic: they are lifts of closed geodesics of a torsion-free cocompact group.

**No wall triangles.** Three pairwise crossing walls are concurrent. Otherwise they bound a compact triangle.
Its interior contains a whole tile, since tile interiors miss all walls. But a triangle has area `< π`, while a
tile has area `(4g−2)π − 4g·π/(2g) = (4g−4)π ≥ 4π`.

**Orientations.**
- For `f ∈ Y_R` with `R ≥ 2g`, opposite edges of a face are dual to one wall and oriented alike, as in a distance
  pattern. So `f` defines a choice `o(W)` of open halfplane, its descending side, for every wall.
- `f` is determined by `o`: `f(y) − f(x)` counts the separating walls with `x ∈ o(W)`, minus those with
  `y ∈ o(W)`.
- `∇d(·,q)` is the orientation with every `o(W) ∋ q`.
- The `Y_R` rule says precisely that `o`, restricted to the walls dual to edges of any `B_R(v)`, is realized by a
  point `q_v` (**local realizability**).

**Claim: `o` is finitely realizable** (every finite `F` has a vertex `x_F ∈ ⋂_{W∈F} o(W)`).
- *Enough.* Then `f = d(·,x_F) + c` on `B_n(1)` whenever `F` contains all walls dual to edges of `B_n(1)`. Every
  path inside the ball crosses only those walls. So `f ∈ K_h`.
- *Reduction to pairs and concurrent triples (Helly in `H²`).* A nonempty finite intersection of open halfplanes
  contains a tile, hence a vertex. By Helly's theorem in the Klein model, it suffices that every 2 and every 3 of
  the `o(W)` intersect.
  - *Triples with two disjoint lines.* Let `L_1 ∩ L_2 = ∅` with `o_1 ∩ o_2 ≠ ∅`.
    - Either `o_1 ⊆ o_2` (or the reverse), or `o_1 ∩ o_2` is the strip `Z` between the lines, with `o_1 ∪ o_2 = H²`.
    - In the strip case, a halfplane `o_3` meeting both `o_1 \ Z` and `o_2 \ Z` meets `Z`, by convexity.
    - So pairwise intersection gives triple intersection.
  - *Triples of pairwise crossing walls.* These are concurrent at some `p` (no triangles). All `2g` walls through
    `p` are dual to one face, which lies in a ball `B_R(v)`, so local realizability gives a common point.
  - *Crossing pairs.* These meet at a dual vertex, handled the same way.
- *Disjoint pairs.* Suppose some disjoint `W_1, W_2` have `o(W_1) ∩ o(W_2) = ∅` ("pointing away").
  - Choose such a pair with `D = d_{H²}(W_1,W_2)` minimal. The minimum is attained, since `Γ_g` has finitely many
    orbits of wall pairs at bounded distance.
  - Let `σ` be the common perpendicular, with feet `a_1, a_2`.
  - (i) **No wall crossing `σ` misses both `W_i`.**
    - Such a wall `V` separates `W_1` from `W_2`.
    - If `o(V)` is the side containing `W_2`, then `o(V) ∩ o(W_1) = ∅`. If it is the side containing `W_1`, then
      `o(V) ∩ o(W_2) = ∅`.
    - Either way this gives a pointing-away pair at distance `< D`.
  - (ii) **Walls crossing `σ` and `W_1` do so near `a_1`.**
    - Let `V` cross `W_1` at `b` and `σ` at `s`. The crossing angle `θ` is a positive multiple of `π/(2g)`.
    - In the right triangle `a_1 b s`: `tan θ = tanh d(a_1,s) / sinh d(a_1,b)`.
    - So `sinh d(a_1,b) < cot(π/(2g))`, i.e. `d(a_1,b) < u_0 := arsinh cot(π/(2g))`.
    - At most `M = M(g)` walls meet a segment of length `2u_0`. The same holds at `a_2`.
  - (iii) **Counting.**
    - `σ` crosses at least `D/d_c − 1` distinct walls, where `d_c` is the tile diameter.
    - By (i) and (ii) there are at most `2M` of them.
    - So `D ≤ D_0 := d_c(2M+1)`.
  - (iv) **Local contradiction.** Take `R_0` so large that any two walls at `H²`-distance `≤ D_0` are dual to edges
    of one ball `B_{R_0}(v)` (Cayley graph and `H²` are quasi-isometric). For `R ≥ R_0`, local realizability puts
    `q_v` in `o(W_1) ∩ o(W_2)`. Contradiction. ∎

## Template for general (HL) (for bh-g2-buildings)

The proof has three moves, and each needs a replacement in a general hyperbolic group:
1. **A halfspace calculus that computes the metric and is locally visible** (here: walls). Then `Y_R` is
   "orientations that are locally realizable".
2. **A Helly number**, which reduces finite realizability to bounded subfamilies. Here: `H²`, with no wall
   triangles; all bounded configurations are seen by one ball.
3. **A descent lemma.** A minimal non-realizable family has bounded diameter. Here: a separating wall always
   shortens a pointing-away pair, and hyperbolic trigonometry bounds the non-separating walls.

In general Cayley graphs there are no walls, and distance patterns only see cone types. The natural substitutes
are:
- for move 1, the cone-type or tail data (parent, 4a);
- for move 3, the CP 2001 horosphere pieces `R_{φ,t}` (their Prop. 3.4).

Moves 1 and 2 are exactly where a general proof must work.

## Lesson for general BH

- Local-to-global for horofunctions is a Helly statement. A locally realizable choice of halfspaces is globally
  realizable once the halfspace system has a Helly number and minimal obstructions have bounded size, and
  negative curvature bounds them. That gives the first one-ended (IE′) examples beyond products: every closed
  surface group has an SFT compactification with a dense seed orbit.
- For the Kazhdan (hyperbolic) case, the missing ingredient is a Helly-type halfspace system. Kazhdan groups
  have no walls (FW), so it must be built from horospheres or cone types instead.

## Referee (bh-ref-hl, 2026-09-18): PASS (now also a special case of `hyperbolic-groups-have-sft-horofunction-compactifications`)

This is an internal lane review.
- **Part 1 (trees).**
  - Out-degree is `≤ 1` from 1-ball patterns.
  - A sink gives `d(·,v)`. Otherwise forward paths merge, and `f − f(1) = b_γ`. Correct.
- **Part 2 (walls).** Every step checks:
  - **Walls.** The Cayley graph is the chamber graph of the reflection group of the dual Coxeter `4g`-gon, whose angles are
    `π/(2g)`. The metric is the separating-wall count.
  - **Non-asymptotic walls.** Each wall has cocompact stabilizer in `Γ_g`: two perpendicular crossing walls give a
    translation along it. A discrete group has no two hyperbolic axes sharing exactly one endpoint.
  - **No wall triangles.** By Gauss–Bonnet, tile area is `(4g−4)π ≥ 4π > π`.
  - **Orientations.** Opposite face edges give a well-defined `o(W)`.
  - **Helly in the Klein model.** The strip and convexity case analysis for pairs and triples is correct.
  - **Minimal pointing-away pair.** A separating wall shortens the pair. The right-triangle formula
    `tan θ = tanh(opp)/sinh(adj)` has `θ` acute, being a non-right angle of a right triangle, and `θ ≥ π/(2g)`, which bounds
    `d(a_1,b) < arsinh cot(π/(2g))`. The count gives `D ≤ d_c(2M+1)`. Local realizability at `R_0` gives the
    contradiction.
- **Minor.** "`σ` crosses at least `D/d_c − 1` walls" is informal but correct up to an additive constant absorbed in `D_0`.
