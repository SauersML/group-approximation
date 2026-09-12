---
rg: 2
id: fpbs-letter-exchange-nonunimodular-proof
kind: route
title: Lift the automorphism group of a directed edge-indexed covering tree that exchanges two letters
target: fpbs-tree-projected-letter-exchange-nonunimodular
requires:
  - fpbs-hyperbolic-and-nonunimodular-nonuniqueness
artifacts:
  - research/artifacts/fpbs/scripts/letter_exchange_rigid_check.py
---

Notation as in the claim. `T = Cay(F_n,B)`: every vertex has one outgoing and one
incoming edge of each label. `X = Cay(Gamma,S)` has vertex set `F_n x Z`,
horizontal edges `(g,m)–(gs,m+d)` for `s in B`, `d in D_s`, and vertical edges
`(g,m)–(g,m+v)` for `(1,v) in S`.

0. **Reduction to translates.** If `D_t = c - D_s`, replace `t` by `t^(-1)` in the
   basis. Then `D_(t^(-1)) = -D_t = D_s - c`, a translate, and `pi(S)` still lies in
   the new basis, its inverses and `1`. So assume `D_t = D_s + c`. Put
   `O = B \ {s,t}`.
1. **Edge-indexed graph.** Let `A` have vertices `u, w, x` and these directed edges,
   written `tail -> head (index at tail : index at head)`:
   * *exchange edges* `e1 = u->w (2:1)`, `e2 = w->x (1:2)`, `e3 = x->w (1:1)`,
     `e4 = x->u (1:1)`, `e5 = w->u (1:1)`;
   * for each `o in O`, three `o`-edges `u->w`, `w->x`, `x->u`, each `(1:1)`.

   At every vertex the exchange tail indices sum to 2 and the exchange head indices
   sum to 2: `u` has tails `e1` (2) and heads `e4, e5` (1+1); `w` has tails `e2, e5`
   and heads `e1, e3`; `x` has tails `e3, e4` and head `e2` (2). For each `o`, every
   vertex has one tail end and one head end of index 1. `A` has no loops.
2. **Covering tree and its group.** As in step 2 of
   `fpbs-reversible-letter-nonunimodular-proof`, let `p : Y -> A` be a covering tree:
   for every vertex `y` over `a` and every edge end `epsilon` of `A` at `a`, exactly
   `i(epsilon)` edges at `y` lie over the edge of `epsilon` with `y` at that end.
   Orient each edge of `Y` as its image.
   * *Extension lemma* (same proof, ball by ball): a `p`-preserving bijection between
     the edges at two vertices over the same vertex extends to an automorphism
     `phi` of `Y` with `p o phi = p`.
   * `G_A = {phi : p o phi = p}` is closed and has three vertex orbits.
   * Every `phi in G_A` keeps the orientation of every edge, because each edge of `A`
     joins two different vertices, so its tail and head lie in different fibres.
3. **Identification with `T`.** Each vertex of `Y` has two outgoing and two incoming
   exchange edges, and one outgoing and one incoming edge over each `o`. Label the
   exchange edges `s` or `t` outward from one vertex, so that every vertex gets one
   outgoing and one incoming edge of each label; label `o`-edges `o`. Then `Y ≅ T` as
   labelled oriented graphs. Transport `G_A` to `Aut(T)`. Each `phi in G_A` maps
   `o`-edges to `o`-edges and exchange edges to exchange edges, keeping orientations,
   and may exchange the labels `s` and `t`.
4. **Height potential and lift.** For an oriented edge `epsilon` of `T` put
   `tau(epsilon) = c` if `epsilon` is a `t`-edge traversed along its label,
   `tau(epsilon) = -c` if traversed against it, and `0` otherwise. Let `D(epsilon)`
   be the set of height changes of `X`-edges over `epsilon`: `D_label` along the
   label and `-D_label` against it. Since `D_t = D_s + c`:
   * along an exchange edge, `D(epsilon) = D_s + tau(epsilon)`;
   * against an exchange edge, `D(epsilon) = -D_s + tau(epsilon)`;
   * on `o`-edges, `tau = 0` and `phi` keeps the label.

   `phi` keeps orientations, so `D(phi epsilon) = D(epsilon) + delta_phi(epsilon)`
   with `delta_phi(epsilon) = tau(phi epsilon) - tau(epsilon)`. This is antisymmetric,
   so on the tree it has a potential `h_phi`. Exactly as in steps 4–5 of the
   reversible-letter proof, `Psi_(phi,k)(g,m) = (phi g, m + h_phi(g) + k)` is an
   automorphism of `X`, and `L = {Psi_(phi,k) : phi in G_A, k in Z}` is a closed group
   with three vertex orbits.
5. **Nonunimodular.**
   * *Stabilizers project isomorphically*, as in step 6 of the reversible-letter
     proof: `Psi_(phi,k)` fixes `(g,m)` iff `phi g = g` and `k = -h_phi(g)`, and a
     `phi` fixing `g, g'` has `delta_phi = 0` on the geodesic between them.
   * *Counting in `G_A`.* Pick `y_0` over `w`. Its only outgoing neighbour over `e2`
     (index 1 at `w`) is `z`, over `x`. The only outgoing neighbour of `z` over `e3`
     (index 1 at `x`) is `y_1`, over `w`.
     * `(G_A)_(y_0)` fixes `z`, then `y_1`. So `|Stab_(y_0) y_1| = 1`.
     * `z` is the only incoming neighbour of `y_1` over `e3` (index 1 at `w`), so
       `(G_A)_(y_1)` fixes `z`. At `z` there are two incoming edges over `e2`
       (index 2 at `x`), one from `y_0`. The bijection of the edges at `z` that swaps
       these two and fixes all others is `p`-preserving, so by the extension lemma
       some `phi in G_A` fixes `z` and `y_1` and moves `y_0`. So
       `|Stab_(y_1) y_0| = 2`.
   * *In `L`.* `y_0` and `y_1` lie in one `G_A`-orbit. Take `phi` with
     `phi y_0 = y_1` and `x' = (y_0,0)`, `y' = Psi_(phi,0)(x')`. Then
     `|Stab_(x') y'| = 1` and `|Stab_(y') x'| = 2`, so `L` is nonunimodular in the
     sense of Section 1 of arXiv:1711.02590v3.
   * *Cross-check.* The Bass–Kulkarni equations `N(tail) i_tail = N(head) i_head`
     have no positive solution: `e1` gives `N(w) = 2N(u)`, `e2` gives
     `N(x) = N(w)/2 = N(u)`, and `e3` demands `N(x) = N(w)`.
6. **Conclusion.** `L` is a closed, quasi-transitive, nonunimodular subgroup of
   `Aut(X)`. Hutchcroft arXiv:1711.02590v3 Theorem 1.2, recorded in
   `fpbs-hyperbolic-and-nonunimodular-nonuniqueness` item 2, gives `p_c(X) < p_u(X)`.

**Check.** `research/artifacts/fpbs/scripts/letter_exchange_rigid_check.py` draws
random automorphisms of the radius-5 ball of `T` that keep orientations and exchange
`a` with `b` (translate mode) or `a` with `b^(-1)` (reflected mode), lifts them with
`tau`, and tests every lifted horizontal edge. It also checks the index sums of `A`
and the failure of the unimodularity equations, and runs a rigid control that must
fail for every shift.
