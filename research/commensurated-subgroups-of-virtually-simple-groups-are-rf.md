---
rg: 2
id: commensurated-subgroups-of-virtually-simple-groups-are-rf
kind: claim
title: In a group with an infinite simple subgroup of finite index, every commensurated subgroup of infinite index is residually finite, so vertex stabilizers of locally finite actions and all slices of virtually simple lattices in products are residually finite
---

**ESTABLISHED** (lane proof, elementary, not reviewed). Items 1–2 are almost certainly known; residual
closures of commensurated subgroups have been studied by Caprace, Kropholler, Reid and Wesolek, but we
have not checked their statements. Item 7 is standard (Malcev). No priority is claimed for items 1–4 and 7.
We have not seen the three-tree consequence (item 6) stated.

Notation: `H^(∞)` is the intersection of all finite-index subgroups of `H` (the finite residual).
`g` **commensurates** `H` if `H ∩ gHg^{-1}` has finite index in `H` and in `gHg^{-1}`. `H` is
commensurated in `G` if every `g ∈ G` commensurates it.

## Statement

1. **Finite index.** If `K ≤ H` has finite index, then `K^(∞) = H^(∞)`.
2. **Commensurators normalize finite residuals.** If `g` commensurates `H`, then `g H^(∞) g^{-1} = H^(∞)`.
   So if `H` is commensurated in `G`, then `H^(∞)` is a normal subgroup of `G`.
3. **Virtually simple groups.** Let `G` have an infinite simple subgroup `S` of finite index. Then every
   commensurated subgroup `H ≤ G` of infinite index is residually finite. If `G` is itself simple, every
   proper commensurated subgroup is residually finite.
4. **Locally finite actions.**
   - Setting: `G` as in item 3 acts on a connected, locally finite graph `Y` with an infinite orbit.
   - Conclusion: every vertex stabilizer is residually finite, and so is every subgroup of `G` with a
     finite orbit on the vertices.
   - The same holds for locally finite CAT(0) cell complexes. There, a subgroup with a bounded orbit
     fixes a point, hence stabilizes a cell.
   - Example: if a simple group splits as `A *_C B` or `A *_C` with `C` of finite index in the vertex
     groups, then its vertex groups are residually finite.
5. **Lattices in products.** Let `Λ ≤ Aut(Y_1) × … × Aut(Y_n)` be a cocompact lattice, with each `Y_i`
   a locally finite, unbounded CAT(0) cell complex, and let `Λ` have an infinite simple subgroup of
   finite index. Then every subgroup of `Λ` with a bounded orbit in some factor `Y_i` is residually
   finite. This includes:
   - every slice group, i.e. the stabilizer of `{y} × ∏_{j≠i} Y_j`;
   - the stabilizer of every convex subcomplex `C_1 × … × C_n` in which some `C_i` is bounded.
6. **Three trees.** Let `Λ ≤ Aut(T_1) × Aut(T_2) × Aut(T_3)` be a virtually simple cocompact lattice of
   locally finite trees.
   - Every non-residually-finite subgroup of `Λ` has unbounded orbits on all three trees.
   - No such subgroup preserves a convex subcomplex that is a product of two trees (such a subcomplex is
     `C_1 × C_2 × C_3` with one `C_i` a vertex or an edge).
   - If `Λ` is a `(d_1,d_2,d_3)`-group, each of its three 2-dimensional sub-data (the generators of two
     types together with their squares) defines a residually finite `(d_i,d_j)`-group.
   - So a non-residually-finite `(d,d')`-group (Wise, Burger–Mozes, Janzen–Wise/Radu `Γ_{4,4}`) can never
     be placed in a slice or a hyperplane stabilizer of a virtually simple 3-tree lattice.
7. **Linear factors (Malcev).** Let `G` be finitely generated and as in item 3.
   - Every homomorphism `G → GL_n(K)`, for any field `K`, has finite image.
   - So if `Λ ≤ G_1 × G_2` is a lattice with an infinite simple subgroup of finite index, and `G_1` is a
     real Lie group or a linear algebraic group over a local field, then `pr_{G_1}(Λ)` is finite.
   - For Lie groups, apply this to `Ad ∘ pr`: the image of the simple part lies in the centre, hence is
     trivial.

## Proof

1. **Finite index.**
   - Every finite-index `L ≤ K` has finite index in `H`, so `H^(∞) ⊆ K^(∞)`.
   - For finite-index `M ≤ H`, the group `M ∩ K` has finite index in `K`, so `K^(∞) ⊆ M ∩ K ⊆ M`.
     Hence `K^(∞) ⊆ H^(∞)`.
2. **Commensurators.** Put `K = H ∩ gHg^{-1}`. It has finite index in `H` and in `gHg^{-1}`. By item 1,
   `H^(∞) = K^(∞) = (gHg^{-1})^(∞) = g H^(∞) g^{-1}`.
3. **Virtually simple groups.** `N := H^(∞)` is normal in `G`, by item 2.
   - `S ∩ H` has finite index in `H`, so `N ⊆ S ∩ H`.
   - `N` is normal in `S`, and `S` is simple, so `N = 1` or `N = S`.
   - `N = S` would give `S ⊆ H`, so `H` would have finite index. Hence `N = 1`, i.e. `H` is residually finite.
   - If `G` is simple, take `S = G`.
4. **Locally finite actions.**
   - **Commensurated.** For adjacent vertices `y, y'`, `G_y ∩ G_{y'}` has index at most `deg(y)` in `G_y`,
     because the `G_y`-orbit of `y'` lies among the neighbours of `y`. By connectedness all vertex
     stabilizers are commensurable, and `g G_y g^{-1} = G_{gy}`, so each `G_y` is commensurated in `G`.
   - **Infinite index.** Since some orbit is infinite and the stabilizers are commensurable, every
     orbit is infinite, so every `G_y` has infinite index. Item 3 applies.
   - **Finite orbits.** A subgroup with a finite orbit has a finite-index subgroup fixing a vertex.
     Groups with a residually finite subgroup of finite index are residually finite.
   - **CAT(0) complexes.** Bounded orbits have a circumcentre, so the subgroup stabilizes the open cell
     containing it. That cell has finitely many vertices.
5. **Lattices in products.**
   - `Λ` acts on each locally finite `Y_i` through `pr_i`, and cocompactly, so it has infinite orbits
     there. Apply item 4 to that action.
   - A subgroup with a bounded orbit in `Y_i` has a finite-index subgroup contained in the stabilizer of
     a vertex of `Y_i`.
6. **Three trees.** This is item 5 with `n = 3`, plus two facts.
   - **Convex subcomplexes.** Convex subcomplexes of a product of trees are products of subtrees, and a
     product of two unbounded trees inside `T_1 × T_2 × T_3` has one bounded factor.
   - **Sub-data.** The subgroup generated by the generators of types `i` and `j` fixes the base vertex
     of the third tree under `pr_k`. It is the full slice stabilizer, since it already acts simply
     transitively on the vertices of the slice.
7. **Linear factors.**
   - A finitely generated linear group is residually finite (Malcev).
   - The image of `S` is therefore a finitely generated linear group, hence residually finite, and it
     is a quotient of the simple group `S`.
   - So it is trivial or isomorphic to `S`. The second is impossible, since `S` is infinite simple and
     hence not residually finite.
   - So the image of `G` is a quotient of the finite group `G/S`.

## Consequences for Kourovka 21.46 (`fp-simple-group-of-finite-cohomological-dimension-above-two`)

- **Three trees need an intrinsically 3-dimensional witness.** Radu (arXiv:1712.01091) found virtually
  simple `(6,6)`- and `(6,8)`-groups by adding squares to the four squares of `Γ_{4,4}`. The
  non-residual finiteness is imported from a 2-dimensional sub-datum.
  - By item 6 this has no three-tree analogue. A virtually simple 3-tree lattice has residually finite
    slices and hyperplane stabilizers, and its non-residual finiteness can only be witnessed by
    subgroups that are unbounded on all three trees.
  - This complements Radu's computational Main Theorem on three trees (no `(6,6,6)`-group with his
    density and local-action hypotheses) with a structural reason why the import strategy cannot work
    there.
- **T × X keeps an import channel.** In Amir–Lazarovich's `T_c × X_{O_d}`, the tree-vertex stabilizers
  are lattices of `Aut(X_{O_d})`, which are virtually Coxeter and hence residually finite. So item 5
  is satisfied.
  - Their non-residually-finite BMW group sits in the stabilizer of `T × H`, with `H` a hyperplane of
    `X`. That subgroup is unbounded on both factors and is not commensurated.
  - Such subgroups exist because `X_{O_d}` is not a product of trees: its hyperplanes are trees that are
    not factors.
  - This is exactly why a 2-dimensional non-residually-finite certificate can be imported into `T × X`
    but not into `T × T × T`.
- **No real or algebraic factors.** By item 7, `ℍ^n × T` and a Bruhat–Tits building times a tree
  carry no virtually simple cocompact lattice: its projection to the non-compact linear factor would be
  finite. For example, graphs of
  cocompact Fuchsian groups glued by elements of the commensurator are torsion-free lattices in
  `PSL_2(ℝ) × Aut(T)` of cohomological dimension 3, but they are never virtually simple. Every factor
  must be totally disconnected and non-linear.

## Lesson for general BH

- **Commensurated means residually finite.** In a simple host, a proper commensurated subgroup is
  residually finite. So a non-residually-finite input can never:
  - lie in a vertex group of a splitting of the host with finite-index edge groups;
  - fix a vertex of a locally finite tree or graph on which the host acts (with an infinite orbit);
  - be commensurated by the host.
- **Examples.** A non-residually-finite group with property (FA) embeds in no simple group that acts
  without a global fixed point on a locally finite tree. Burger–Mozes-type hosts can hold only
  residually finite groups in their vertex groups.
- **Diagonal carriers.** Hosts must carry non-residually-finite inputs *diagonally*, with unbounded
  orbits on every locally finite factor, and through non-commensurated carriers such as hyperplane
  stabilizers. This is the carrier principle of SYNTHESIS, sharpened: the carrier of the hardness is
  never a commensurated subgroup of the host.
