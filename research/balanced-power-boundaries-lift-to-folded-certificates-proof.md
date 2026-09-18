---
rg: 2
id: balanced-power-boundaries-lift-to-folded-certificates-proof
kind: route
title: Raise genus by a Z/3 cover, equalise exponents by an S_D cover with even monodromy (Ore), match circles, then realise LP points by the positions construction
target: balanced-power-boundaries-lift-to-folded-certificates
requires:
  - legal-f-folded-fatgraphs-give-surface-subgroups
  - positive-f-folded-fatgraphs-have-only-even-valence
  - power-two-word-free-census-of-power-one-silent-classes
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lift_lp.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lift_word.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface_multi.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface_phi939_phi4010_m2.log
---

Standard facts used, not re-read at source:

- (S1) Finite covers of a compact surface `S`, possibly disconnected, correspond to actions
  of `pi_1(S)` on finite sets.
- (S2) A connected compact orientable surface of genus `gamma` with `b >= 1` boundary
  circles has `pi_1 = < a_1, b_1, ..., a_gamma, b_gamma, c_1, ..., c_b | prod [a_i, b_i] c_1 ... c_b >`,
  where `c_j` is freely homotopic to the `j`-th boundary circle, up to orientation.
- (S3) Ore (Proc. AMS 2 (1951) 307--314): every even permutation of `{1, ..., D}` is a
  commutator `[alpha, beta]` with `alpha, beta` in `S_D`.
- (S4) A cyclically reduced word `z` is a proper power as a cyclic word if and only if its
  conjugacy class in `F` consists of proper powers. Conjugates of proper powers are proper
  powers.

Conventions are those of `lp5.py` and `ffold.py`.

- A fatgraph is a finite set of darts with a fixed-point-free involution `p` (the edges),
  labels with `label(p x) = label(x)^{-1}`, and a boundary successor `nxt`.
- Vertices are the cycles of `sigma = nxt o p`, and boundary circles are the cycles of `nxt`.
- The corner preceding a dart `x` sits at the vertex of `x`. That corner carries the marks of
  `x`: its kind (`-` or `+`) and whether it is an `f`-corner.
- The thickening `S(X)` is an orientable surface with `chi(S(X)) = chi(X)`, and its boundary
  circles are the cycles of `nxt`.

**Step 1: covers.** Let `pi: X~ -> X` be the restriction to the spine of a finite cover of
`S(X)` of degree `k` (S1), with labels and marks pulled back.

1. `pi` is an isomorphism on the ribbon neighbourhood of every vertex and every edge.
   Conditions (L), (2), (3), (4) are statements about such a neighbourhood and its marks, so
   they hold on `X~`.
2. Let `C` be a boundary circle of length `L` whose monodromy (the permutation of the sheets
   given by going once around `C`) has a cycle of length `l`. That cycle gives one circle
   of `X~` of length `lL`. It reads the cyclic word of `C` `l` times, and it has the same kind.
   - For a `-` circle it reads `u_C^{l e_C}`.
   - For a `+` circle it carries `v_C^{l e_C}`, with its `f`-corners still at the block starts.
   - The roots `u_C` and `v_C` do not change.
3. `chi(X~) = k chi(X)`.

**Step 2: components.** Let `Y` be a component of `X`.

1. By (P), every boundary circle reads a nonempty cyclically reduced word. For a `+` circle
   this is `f(v_C)^{e_C}`, which is cyclically reduced because `f(v_C)` is.
2. A 1-valent vertex would give a circle that backtracks (`x` followed by `x^{-1}`), so `Y`
   has no 1-valent vertex. Hence `chi(Y) = V - E <= 0`.
3. `chi(Y) = 0` exactly when every vertex is 2-valent, that is, when `Y` is a cycle. Then
   `S(Y)` is an annulus, and its two circles read `z` and `z^{-1}` for one cyclic word `z`.
   The two circles have equal exponents:
   - If a circle is `-` and reads `u^e`, then `e` is the exponent of `z`.
   - If a circle is `+` with `v^e`, then it reads `f(v)^{-e}`. `f(v)` is cyclically reduced,
     and it is not a proper power as a cyclic word. Otherwise, by (S4), `phi(v)` would be
     conjugate to some `r^j` with `j >= 2`, so `v` would be conjugate to `phi^{-1}(r)^j`,
     contradicting the primitivity of `v`. So `e` is again the exponent of `z`.
4. If `chi(Y) < 0` and `S(Y)` has genus 0, then `S(Y)` has `b = 2 - chi(Y) >= 3` circles.

**Step 3: raise the genus (degree 3).** Build a degree-3 cover of each component `Y`.

1. **Planar `Y` with `chi(Y) < 0`.** By (S2), `pi_1(S(Y))` is free on `c_1, ..., c_{b-1}`,
   with `c_b = (c_1 ... c_{b-1})^{-1}`.
   - Send `c_1, c_2, c_3` to `1` in `Z/3` and every other `c_j` to `0`. The sum over all
     `j` is `3 = 0`, so this is a homomorphism. It is onto, so the cover is connected.
   - The circles `c_1, c_2, c_3` lift to one circle each, and every other circle lifts to
     three.
   - The cover has `chi' = 3 chi(Y) = 6 - 3b` and `b' = 3 + 3(b - 3) = 3b - 6` circles. So
     its genus is `(2 - chi' - b')/2 = 1`.
2. **Every other `Y`.** Take three disjoint copies.

The result `X'` again satisfies (L), (2), (3), (4) and (P) by Step 1, and `chi(X') = 3 chi(X) < 0`.

(B) still holds. A circle with monodromy of order 3 becomes one circle with exponent
`3 e_C`. A circle with trivial monodromy becomes three circles with exponent `e_C`. Either
way, the exponent sum over the lifts of `C` is `3 e_C`, with the same root.

Every component of `X'` with `chi < 0` has genus `>= 1`. Every component with `chi = 0` is
an annulus whose two circles have equal exponents (Step 2).

**Step 4: equalise the exponents (degree `D`).** Choose the degree and the cycle lengths.

- Let `E` be the lcm of all `e_C` over the circles of `X'`.
- For each circle `C`, let `l_C = E / e_C`.
- Let `M` be the lcm of the `l_C`, and let `D = 2M`.
- For each circle `C`, choose `tau_C` in `S_D` with `D / l_C` cycles, all of length `l_C`.
  Its sign is `(-1)^{(l_C - 1) D / l_C} = +1`, because `D / l_C = 2M / l_C` is even.

Build a degree-`D` cover of each component `Y` of `X'`.

- **Genus `>= 1`.** Order the circles as in (S2). The product `pi = tau_{C_1} ... tau_{C_b}`
  is even, so by (S3) `pi^{-1} = [alpha, beta]`. Send `c_j` to `tau_{C_j}`, `a_1` to `alpha`,
  `b_1` to `beta`, and every other generator to `1`. The relator maps to
  `[alpha, beta] pi = 1`.
- **Annulus.** `pi_1 = Z`, and both circles are freely homotopic to the core up to
  orientation. Send the core to `tau_{C_1}`. The monodromies of the two circles are
  `tau_{C_1}^{±1}`, which have the cycle type `l^{D/l}` with `l = l_{C_1} = l_{C_2}`,
  because the exponents are equal.

Let `X~` be the union of the corresponding covers (S1). The cover may be disconnected.

By Step 1, `X~` satisfies (L), (2), (3), (4), and `chi(X~) = D chi(X') = 3D chi(X) < 0`.
Each circle `C` has monodromy conjugate to `tau_C^{±1}`. So `C` has exactly `D / l_C = D e_C / E`
lifts, and each of them reads `u_C^E` (a `-` circle) or carries `v_C^E` (a `+` circle).

**Step 5: match.** Fix a primitive cyclic word `u`. By (B), the number of `-` circles of
`X~` reading `u^E` is `(D/E) sum e_C` over the `-` circles of `X'` with root `u`. The number
of `+` circles carrying `u^E` is `(D/E) sum e_C` over the `+` circles of `X'` with root `u`.
These are equal. For `X'`, (B) holds by Step 3.

Pair these circles by any bijection, for every `u`. On a `-` circle, choose the base point
at the start of a period `u`, so that it reads `w = u^E`. On its partner, choose the base
point at the start of the block `f(y_1)^{-1}` of a period `u`. The partner then reads
`f(u^E)^{-1} = f(w)^{-1}`, with its `f`-corners at the block starts. So `X~` is an
`f`-fatgraph with matched boundary that satisfies (L), (2), (3), (4).

By Step 5 of `legal-f-folded-fatgraphs-give-surface-subgroups-proof`,
`S*_f(X~) -> K` is `pi_1`-injective component by component, and
`chi(S*_f(X~)) = chi(X~) < 0`.

That argument does not use connectivity of `X~`. Step 0 lifts a loop to the cyclic cover.
Step 0 part 2 and Steps 1--4 collapse track trees and show that each component of `X_n`
immerses. So some component of `S*_f(X~)` is a closed orientable surface of genus `>= 2`
whose fundamental group injects into `K`, and hence into `F x|_phi Z`. `QED` (Theorem)

**Step 6: the positions construction (Corollary).** Scale a rational solution `(y, n)` with
`chi < 0` to an integer solution. The system is homogeneous, and `chi < 0` is invariant
under positive scaling.

1. **Positions.** Let `Omega` be the set of triples `(P, i, s)`: a polygon `P`, a copy
   `i < y_P`, and a slot `s` in `Z/|P|`. Write the slots of `P` as `(d_s -> q_s)`, with
   `label(q_s) = label(d_s)^{-1}` and `d_{s+1} = nxt_B(q_s)`.
   - Set `typ(P, i, s) = d_s` and `sigma(P, i, s) = (P, i, s + 1)`.
   - The pair row for `{d, q}` says that exactly as many positions have slot `(d -> q)` as
     have slot `(q -> d)`, and `d != q` because the labels are inverse. Choose any
     bijection between these two sets. This defines a fixed-point-free involution `p` with
     `typ(p x) = q_s` when `x` has slot `(d_s -> q_s)`. In particular the labels are
     inverse.
   - Set `nxt = sigma o p`. Then the vertices, the cycles of `nxt o p = sigma`, are exactly
     the polygon copies. Pull back the kind and the `f`-mark from `typ`.
2. **Local conditions.** At a vertex (a copy of `P`), the directions are the labels of the
   `d_s`, and the marks are those of the `d_s`. The edge of `x` joins darts of types `d_s`
   and `q_s`. The constraints built into `lp5.polygons` are therefore exactly (L), (2),
   (3), (4) at this vertex and on these edges:
   - the gates of the `d_s` are pairwise distinct;
   - at most one `d_s` is an `f`-dart, and then `|P| = 2`;
   - at most one `d_s` is a `partial^-` dart;
   - no slot joins two `partial^-` darts;
   - `|P| >= 2`.
3. **Types follow the boundary of `B`.** If `z = p(x)` and `x` has slot `(d_s -> q_s)`,
   then `typ(nxt z) = typ(sigma x) = d_{s+1} = nxt_B(q_s) = nxt_B(typ z)`. So the types
   along any circle of `X` follow one circle `C_B` of `B`. That circle of `X` has length
   `k |C_B|`, reads the word of `C_B` `k` times, and keeps the block structure of a `+`
   circle.
   - The row of a dart `d` of `C_B` says that `n_w` positions have type `d`. Summing over
     the `|C_B|` darts of `C_B` gives `sum k = n_w`, over the circles of `X` above `C_B`.
   - This holds for the `-` circle of `w` and for the `+` circle of `w`.
4. **(P) and (B).** Write `w = u^j` with `u` primitive. A `-` circle above `w` reads `u^{jk}`,
   and a `+` circle above `w` carries `u^{jk}`. `w^k` is cyclically reduced, and `f(u)` is
   cyclically reduced because `f(w) = f(u)^j` is. So (P) holds. For each root `u`, both
   exponent sums in (B) equal `sum_{w in W, w = u^j} j n_w`.
5. **Conclusion.** `chi(X) = V - E = sum_P y_P - sum_P y_P |P|/2 < 0`. So `X` is a balanced
   power fatgraph, and the Theorem gives the surface subgroup. For one word with
   `n_w = N`, the rows are those of `lp5.solve_lp` scaled by `N`.
6. **Converse.** Step 8 of `positive-f-folded-fatgraphs-have-only-even-valence-proof`
   projects a certificate with boundary made of copies of `w` to a feasible point with the
   same `chi`, for a positive `phi` and a legal cyclic word `w`. Its last paragraph leaves
   the converse open, and Steps 1--5 above prove it. `QED` (Corollary)

**Step 7: entries 939 and 4010.** The certificates were produced by `lift_lp.py --perm`,
but they do not rely on that construction. Each JSON file lists the labels, the pairing
and the `partial^-` words.

1. **Checker output.** `verify_surface_multi.py` recomputes, from the file alone:
   - an explicit inverse of `phi`, `M^2 > 0`, and that `chi_M` is a cubic with no rational
     root;
   - the gates of `phi^2`, and (L), (2), (3), (4) at every vertex and edge;
   - that every `partial^-` circle `w` is followed by a circle reading `f(w)^{-1}` with its
     `f`-corners at the block starts;
   - the number of components of `S*_f(X)` (`1`), and `chi(X)`.

   `verify_surface.py` performs the same checks and also requires `X` connected. It passes
   on 939 and fails only that requirement on 4010, whose `X` has two components. The
   outputs are in `verify_surface_phi939_phi4010_m2.log`.
2. **Surface subgroup.** By Step 5 above (disconnected `X` allowed), `S*_f(X)` is a closed
   orientable surface with `chi = -24` (genus 13) for 939, and `chi = -4` (genus 3) for
   4010, and its fundamental group injects.
3. **Hyperbolicity.** Step 5 of `power-two-word-free-census-of-power-one-silent-classes-proof`
   uses only `M^k > 0` and an irreducible cubic `chi_M`. So `phi` is fully irreducible and
   atoroidal, and `G` is one-ended and hyperbolic.
4. **Invariants.** `chi_M(1) = 1 - 3 + 1 - 1 = -2` for 939, and `1 - 3 - 1 + 1 = -2` for 4010.
   So `|H_1(G)_{tors}| = |det(M - I)| = 2` in both cases.
