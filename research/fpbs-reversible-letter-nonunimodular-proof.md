---
rg: 2
id: fpbs-reversible-letter-nonunimodular-proof
kind: route
title: Lift the automorphism group of an edge-indexed covering tree that reverses only one letter
target: fpbs-tree-projected-reversible-letter-nonunimodular
requires:
  - fpbs-hyperbolic-and-nonunimodular-nonuniqueness
artifacts:
  - research/artifacts/fpbs/scripts/reversible_letter_lift_check.py
---

Notation as in the claim. In `T = Cay(F_n,B)` every vertex has one outgoing and
one incoming edge of each label. `X = Cay(Gamma,S)` has vertex set `F_n x Z` and
two kinds of edges:
* horizontal edges `(g,m)–(gs,m+d)` for `s in B`, `d in D_s`;
* vertical edges `(g,m)–(g,m+v)` for `(1,v) in S`.

Put `O = B \ {s_0}`, which is nonempty since `n >= 2`.

1. **Edge-indexed graph.** Let `A` be the finite graph with vertices `u, w, x`
   and these edges:
   * two `s_0`-edges: `e = {u,w}` with index 2 at `u` and 1 at `w`, and
     `f = {w,x}` with index 1 at `w` and 2 at `x`;
   * for each `o in O`, three `o`-edges `u -> w`, `w -> x`, `x -> u`, each with
     index 1 at both ends.

   Write `i(epsilon)` for the index at an edge end `epsilon`. At each vertex:
   * the `s_0`-edge ends have indices summing to 2;
   * for each `o`, the outgoing and the incoming `o`-edge end each have index 1.

   `A` has no loops.
2. **Covering tree and its group.** Let `Y` be a tree with a map `p : Y -> A` on
   vertices and edges with the following property. For every vertex `y` over `a`
   and every edge end `epsilon` of `A` at `a`, exactly `i(epsilon)` edges at `y`
   map onto the edge of `epsilon`, with `y` at that end. Such a `Y` exists: grow
   it outward from one vertex.
   * *Extension lemma.* Let `y, y'` lie over the same vertex, and let `beta` be a
     bijection from the edges at `y` to the edges at `y'` with `p o beta = p`.
     Then some automorphism `phi` of `Y` with `p o phi = p` extends `beta`.
     *Proof.* Extend ball by ball. A vertex `z` at distance `r >= 1`, entered
     through the edge end `eta`, has `i(epsilon) - [epsilon = eta]` further edges
     over each end `epsilon` at `p(z)`. Its image has the same counts, so any
     `p`-preserving bijection of these edges extends the map.
   * Let `G_A = {phi in Aut(Y) : p o phi = p}`. It is closed, because
     `p o phi = p` is tested pointwise. By the lemma it is transitive on each
     fibre of `p`, so it has three vertex orbits.
   * By the lemma, `(G_A)_y` permutes the `i(epsilon)` edges over `epsilon` at `y`
     transitively. An automorphism fixing both ends of an edge fixes the edge.
     So for an edge `{y,z}` whose ends lie over `epsilon` (at `y`) and `epsilon'`
     (at `z`):
     * `[(G_A)_y : (G_A)_y ∩ (G_A)_z] = i(epsilon)`;
     * `[(G_A)_z : (G_A)_y ∩ (G_A)_z] = i(epsilon')`.
3. **Identification with `T`.** Every vertex of `Y` has two `s_0`-edges, so the
   `s_0`-edges form bi-infinite lines. Orient each line consistently, and orient
   each `o`-edge as in `A`. Now every vertex has one outgoing and one incoming
   edge of each label, so `Y ≅ T` as labeled oriented graphs. Build the
   isomorphism outward from one vertex, and transport `G_A` into `Aut(T)`.
   * Each `phi in G_A` maps `o`-edges to `o`-edges and keeps their orientation,
     because the two ends of an `o`-edge of `A` lie over different vertices.
   * It maps `s_0`-edges to `s_0`-edges, possibly reversed.
4. **Height potential and lift.**
   * For an oriented edge `epsilon` of `T`, put `tau(epsilon) = -c` if `epsilon`
     is an `s_0`-edge traversed against its label, and `tau(epsilon) = 0`
     otherwise.
   * Let `D(epsilon)` be the set of height changes of `X`-edges over `epsilon`:
     `D_s` along the label `s`, and `-D_s` against it. Since
     `-D_(s_0) = D_(s_0) - c`, we get `D(epsilon) = D_(label) + tau(epsilon)` for
     `s_0`-edges.
   * Hence `D(phi epsilon) = D(epsilon) + tau(phi epsilon) - tau(epsilon)` for
     every `phi in G_A` and every oriented edge `epsilon`.
   * `delta_phi(epsilon) = tau(phi epsilon) - tau(epsilon)` is antisymmetric. So
     on the tree `T` it has a potential `h_phi`, unique up to a constant, with
     `h_phi(g') - h_phi(g) = delta_phi(g -> g')`.
   * `Psi_(phi,k)(g,m) = (phi g, m + h_phi(g) + k)` maps vertical edges to vertical
     edges. Take a horizontal edge over `epsilon = (g -> g')` with height change
     `d in D(epsilon)`. Its image lies over `phi epsilon`, with height change
     `d + delta_phi(epsilon) in D(phi epsilon)`, so it is an edge of `X`. The
     inverse of `Psi_(phi,k)` is a lift of `phi^(-1)`, so `Psi_(phi,k) in Aut(X)`.
   * `L = {Psi_(phi,k) : phi in G_A, k in Z}` is a group, because
     `delta_(phi psi)(epsilon) = delta_psi(epsilon) + delta_phi(psi epsilon)`.
5. **Closed, with three orbits.**
   * Suppose `Psi_(phi_j,k_j) -> Psi` pointwise. Then `phi_j -> phi` pointwise and
     `phi in G_A`. For each `g`, `h_(phi_j)(g) - h_(phi_j)(1)` depends only on
     `phi_j` along the geodesic from `1` to `g`, so eventually it equals
     `h_phi(g) - h_phi(1)`. Reading heights at `(1,0)`, the total shift is
     eventually constant. So `Psi = Psi_(phi,k)` for some `k`, and `L` is closed.
   * `k` shifts heights, so `(g,m)` and `(g',m')` lie in one `L`-orbit iff `g` and
     `g'` lie in one `G_A`-orbit. So `L` has three vertex orbits.
6. **Nonunimodular.**
   * *Stabilizers project isomorphically.* `Psi_(phi,k)` fixes `(g,m)` iff
     `phi g = g` and `k = -h_phi(g)`. If `phi` fixes `g` and `g'`, it fixes every
     edge of the geodesic between them. Then `delta_phi = 0` along it, and
     `h_phi(g) = h_phi(g')`. So for `x = (g,m)` and `y = (g',m')`, projection maps
     `L_x` onto `(G_A)_g` and `L_x ∩ L_y` onto `(G_A)_g ∩ (G_A)_(g')`, both
     bijectively, and the indices agree.
   * *Counting in `G_A`.* Pick `y_0` over `u`, the outgoing `o`-edge from `y_0` to
     `z` over `w`, and the `s_0`-edge over `e` from `z` to `y_1` over `u`.
     * `(G_A)_(y_0)` fixes `z`, the only neighbour of `y_0` over `u -> w`. It then
       fixes `y_1`, the only neighbour of `z` over `e`. So
       `|Stab_(y_0) y_1| = 1`.
     * `(G_A)_(y_1)` moves `z` transitively over the 2 neighbours of `y_1` over
       `e` (step 2). The image of `y_0` is the only neighbour of the image of `z`
       over `u -> w`. So distinct images of `z` give distinct images of `y_0`,
       and `|Stab_(y_1) y_0| = 2`.
   * *In `L`.* Take `phi in G_A` with `phi y_0 = y_1`, put `x = (y_0,0)`, and let
     `y = Psi_(phi,0)(x)`. Then `y` lies over `y_1`, in the orbit of `x`. By the
     stabilizer bullet, `|Stab_x y| = 1` and `|Stab_y x| = 2`.
   * *Definition.* Section 1 of Hutchcroft arXiv:1711.02590v3 calls
     `Gamma ⊆ Aut(G)` unimodular if `|Stab_v u| = |Stab_u v|` for all `u, v` in
     one orbit. So `L` is nonunimodular. For a closed group this agrees with the
     Haar-measure definition, because `|Stab_x y| / |Stab_y x| = mu(L_x)/mu(L_y)`.
7. **Conclusion.** `L` is a closed, quasi-transitive, nonunimodular subgroup of
   `Aut(X)`. Hutchcroft arXiv:1711.02590v3, Theorem 1.2 (`thm:pcpu` in the TeX
   source), is recorded in `fpbs-hyperbolic-and-nonunimodular-nonuniqueness`
   item 2. It reads: "Let G be a connected, locally finite graph, and suppose
   that Aut(G) has a quasi-transitive nonunimodular subgroup. Then
   p_c(G)<p_u(G)." So `p_c(X) < p_u(X)`.

**Check.** `research/artifacts/fpbs/scripts/reversible_letter_lift_check.py`
draws random color-preserving automorphisms of the radius-5 ball of `T` that
reverse only permitted letters, and tests every lifted horizontal edge. Run on
MSI on 2026-09-12:
* 0 bad edges for `D_a = {0,1}, D_b = {0}`, reversing `b` or both letters;
* 0 bad edges for `D_a = {0,1,3}, D_b = {0}`, reversing `b`;
* 0 bad edges for `D_a = {0,2,3,5}, D_b = {1,4}`, reversing both;
* the control that reverses `D_a = {0,1,3}` fails for every shift in `[-4,4]`.

**Scope.** Only `Gamma = F_n x Z`. If no letter is symmetric up to translation,
the lifted automorphisms must keep every orientation. Among lifts of
color-preserving automorphisms this leaves the translations by `F_n`, which form
a discrete group. Subgroups that exchange letters with translate decoration
sets, and automorphisms of `X` that are not lifts, are not excluded.
