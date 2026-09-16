---
rg: 2
id: fpbs-twisted-cyclic-by-free-nonunimodular-proof
kind: route
title: Lift the covering-map group of a four-vertex edge-indexed tree to a twisted Cayley graph without a height potential
target: fpbs-tree-projected-twisted-cyclic-by-free-nonunimodular
requires:
  - fpbs-hyperbolic-and-nonunimodular-nonuniqueness
  - fpbs-hyperbolic-nonunimodular-critical-l2-gap
artifacts:
  - research/artifacts/fpbs-twisted-cyclic-by-free-nonunimodular-2026-09-16.md
  - experiments/fpbs-twisted-cyclic-by-free-2026-09-16/twisted_lift_check.py
---

Notation as in the claim. Section 1 of the artifact expands each step.

1. **Normal form.** Let `z` generate `H`. Extend a lift of `B` to a homomorphism
   `sigma : F_n -> Gamma`, and let `chi : F_n -> {±1}` record conjugation on `H`:
   `sigma(g) z sigma(g)^(-1) = z^(chi(g))`. Then `(m,g) -> z^m sigma(g)` is an
   isomorphism from `Z ⋊_chi F_n`, with product
   `(m,g)(m',g') = (m + chi(g) m', g g')`. `H` is central iff `chi = 1`. So fix
   `s_0 in B` with `chi(s_0) = -1`, and put `O = B \ {s_0}`, which is nonempty.
   * Since `pi(S)` generates `F_n`, each `D_s = {d : (d,s) in S}` (`s in B`) is
     nonempty. Put `V = {v : (v,1) in S} = -V`.
   * In `X = Cay(Gamma,S)`, `(m,g)(v,1) = (m + chi(g) v, g)`, so the vertical
     neighbours of `(m,g)` are `(m+V, g)`.
   * `(m,g)(d,s) = (m + chi(g) d, gs)`, and the generators over `s^(-1)` are the
     inverses `(-chi(s) d, s^(-1))`, which give the same edges.
2. **Shape lemma.** Colour `g` by `c(g) = chi(g)`. Orient `e = {g,gs}` as
   `p -> q`, with `(p,q) = (g,gs)` if `c(g) = +1` and `(p,q) = (gs,g)` otherwise.
   * The `X`-edges over `e` are exactly `(m,p)–(m+d,q)` for `m in Z`, `d in D_s`.
     If `c(g) = -1`, then `(m,g)–(m-d,gs)` is `(m',p)–(m'+d,q)` with `m' = m-d`.
   * If `chi(s) = -1`, the ends of an `s`-edge have different colours, and it points
     from `+` to `-`. At a `+` vertex both `s`-edges point out, and at a `-` vertex
     both point in.
   * If `chi(s) = +1`, both ends have the same colour, and each vertex has one
     outgoing and one incoming `s`-edge.

   Call this the *structure* of `T = Cay(F_n,B)`.
3. **Lift without potential.** Let `phi` be an automorphism of `T` preserving
   labels and orientations, and let `k in Z`. Then
   `Psi_(phi,k)(m,g) = (m+k, phi g)` maps vertical edges to vertical edges. It maps
   `(m,p)–(m+d,q)` over the `s`-edge `p -> q` to `(m+k,phi p)–(m+k+d,phi q)`,
   which lies over the `s`-edge `phi p -> phi q`, so it is an edge by step 2. Its
   inverse `Psi_(phi^(-1),-k)` is of the same form. So `Psi_(phi,k) in Aut(X)`.
4. **Edge-indexed graph.** Let `A` have vertices `u, w` (colour `+`) and `x, y`
   (colour `-`), with these edges (index at the first end : index at the second):
   * `s_0`: `e_1 = {u,x}` `2:1`, `e_2 = {x,w}` `1:1`, `e_3 = {w,y}` `1:2`;
   * each `r in O` with `chi(r) = -1`: `{u,x}`, `{x,w}`, `{w,y}`, `{y,u}`, all `1:1`;
   * each `o in O` with `chi(o) = +1`: directed edges `u -> w`, `w -> u`, `x -> y`,
     `y -> x`, all `1:1`.

   At every vertex, the ends of `r`-edges have indices summing to 2 when
   `chi(r) = -1`. When `chi(o) = +1` there is one outgoing and one incoming
   `o`-end, each of index 1. Twisted edges join different colours, untwisted edges
   join equal colours, and `A` has no loops.
5. **Covering tree, extension lemma.** Grow a tree `Y` from `y_0` over `u` with a
   map `p : Y -> A` on vertices and edges. For every `y` over `a` and every edge end
   `epsilon` at `a`, exactly `i(epsilon)` edges at `y` lie over the edge of
   `epsilon`, with `y` at that end.
   * *Extension lemma* (as in step 2 of `fpbs-reversible-letter-nonunimodular-proof`).
     If `y, y'` lie over one vertex and `beta` is a `p`-preserving bijection between
     their edge sets, some `phi in Aut(Y)` with `p o phi = p` extends `beta`. Extend
     ball by ball: a vertex entered through the end `eta` has
     `i(epsilon) - [epsilon = eta]` further edges over each end `epsilon`, and so
     does its image.
   * `G_A = {phi : p o phi = p}` is closed and transitive on each fibre of `p`. The
     fibres are nonempty because `u–x–w–y` is connected by `e_1, e_2, e_3`, so
     `G_A` has four vertex orbits.
   * For an edge `{y,z}` over ends `epsilon` (at `y`) and `epsilon'` (at `z`), the
     group `(G_A)_y` permutes the `i(epsilon)` edges over `epsilon` at `y`
     transitively.
6. **Identification.** Give `Y` the colours of `A`. Orient an edge over a twisted
   edge from its `+` end, and an edge over `a -> b` from its end over `a`. By
   step 4, every vertex of `Y` has the local structure of step 2:
   * two outgoing (at `+`) or two incoming (at `-`) `r`-edges to the other colour,
     for `chi(r) = -1`;
   * one outgoing and one incoming `o`-edge to the same colour, for `chi(o) = +1`.

   Build `iota : Y -> T` with `iota(y_0) = 1`, ball by ball. At a matched vertex,
   match the unmatched edges within each type (label, and direction for untwisted
   letters). The counts agree, because the parent edge has the same type on both
   sides, and each type determines the colour of the far end. A local bijection
   between trees is an isomorphism, so `iota` preserves colours, labels and
   orientations.
   * Each `phi in G_A` preserves colours and labels, which are read from `A`.
   * It preserves orientations: of twisted edges through colours, and of an edge
     over `a -> b` because `p o phi = p` sends the end over `a` to the end over `a`.
   * So `phi' = iota phi iota^(-1)` satisfies step 3.
7. **The group `L`.** Let `L = {Psi_(phi',k) : phi in G_A, k in Z}`.
   * It is a group, since `Psi_(phi,k) Psi_(psi,l) = Psi_(phi psi, k+l)`.
   * It is closed: if `Psi_(phi'_j,k_j) -> Psi` pointwise, then `phi'_j g` and `k_j`
     (the height of the image of `(0,1)`) are eventually constant. Since `G_A` is
     closed, `Psi = Psi_(phi',k)` with `phi in G_A`.
   * `k` is free, so `L` has four vertex orbits.
   * `Psi_(phi',k)` fixes `(m,g)` iff `k = 0` and `phi' g = g`. So `phi -> Psi_(phi',0)`
     maps `(G_A)_(iota^(-1) g)` onto `L_((m,g))`, and
     `(G_A)_y ∩ (G_A)_(y')` onto the intersection of the corresponding stabilizers.
     Indices therefore agree.
8. **Counting.** Pick `t in O`.
   * If `chi(t) = +1`, walk from `y_0`: the `t`-edge over `u -> w` (index 1 at
     `u`) to `z_1`, then over `e_2` (index 1 at `w`) to `z_2`, then over `e_1`
     (index 1 at `x`) to `y_1` over `u`.
   * If `chi(t) = -1`, walk from `y_0`: the `t`-edge over `{u,x}` (index 1 at `u`)
     to `z_2`, then over `e_1` (index 1 at `x`) to `y_1` over `u`.

   Every step has index 1 in the forward direction, and each step uses a different
   `A`-edge from the step before, so no step backtracks. So `(G_A)_(y_0)` fixes
   `y_1`, and `|Stab_(y_0) y_1| = 1`.

   Backward from `y_1`, the first step, over `e_1` at `u`, has index 2 and every
   later step has index 1. By step 5, `(G_A)_(y_1)` moves `z_2` over 2 vertices,
   and the image of `z_2` determines the image of `y_0`. Conversely, the image of
   `z_2` is the neighbour of `y_1` on the geodesic to the image of `y_0`, because
   `Y` is a tree. So `|Stab_(y_1) y_0| = 2`.

   Put `x_0 = (0, iota y_0)` and `x_1 = (0, iota y_1)`. They lie in one `L`-orbit,
   because `y_0, y_1` lie over `u`. By step 7, `|Stab_(x_0) x_1| = 1` and
   `|Stab_(x_1) x_0| = 2`.
9. **Conclusion.** Section 1 of Hutchcroft arXiv:1711.02590v3 calls a subgroup
   unimodular if `|Stab_v u| = |Stab_u v|` for all `u, v` in one orbit. So `L` is a
   closed, quasi-transitive, nonunimodular subgroup of `Aut(X)`.
   * By `fpbs-hyperbolic-and-nonunimodular-nonuniqueness` item 2 (arXiv:1711.02590v3
     Theorem 1.2), `p_c(X) < p_u(X)`.
   * By `fpbs-hyperbolic-nonunimodular-critical-l2-gap` (arXiv:1804.10191
     `thm:nonunimodular`, `q = 2`), `p_c(X) < p_(2->2)(X)`.

**Check.** `experiments/fpbs-twisted-cyclic-by-free-2026-09-16/twisted_lift_check.py`
(run 2026-09-16) tested six twisted cases in ranks 2 and 3. They include the rigid
data `D_a = {0,1,3}`, `D_b = {0,1,4}` under each of the three nontrivial `chi`, and
decoration sets with no symmetry. The script confirms the following.
* The shape lemma, from the group law: 0 bad tree edges.
* The local types of `Y` against `T`: 0 defects, `iota` injective.
* Random elements of `G_A` moving `y_0` to `y_1`, transported to `T` and lifted with
  no potential: 0 bad edges of 7728 (rank 2) or 6732 (rank 3).
* The lift counts `1` and `2` in every case.

The control transports the same automorphisms to the `F_2 x Z` group law and gets
248 bad edges of 1272.
