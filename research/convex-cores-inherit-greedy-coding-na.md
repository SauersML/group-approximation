---
rg: 2
id: convex-cores-inherit-greedy-coding-na
kind: claim
title: If a hyperbolic group G acts on a CAT(0) cube complex X with (NA), every quasiconvex subgroup Q with a Q-cocompact convex subcomplex Y ⊆ X satisfies (NA) on Y; so Q is a contracting RSG as soon as the greedy coding of Y satisfies (IRR), and in particular for quasiconvex subgroups of hyperbolic RACGs only (IRR) remains
distinct_from:
  greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs: that is the conditional theorem for one cubulation; this shows its hypothesis (NA) passes from an ambient cubulation to the convex core of any quasiconvex subgroup.
  contracting-rsgs-pass-to-finite-index-subgroups-via-loops: that handles finite-index subgroups by coset refinement; this handles quasiconvex subgroups of infinite index, where only (NA) passes and (IRR) is left.
  hyperbolic-racgs-with-spread-nerves-are-contracting-rsgs: that proves (NA) for hyperbolic RACGs; with this, (NA) holds for every quasiconvex subgroup of a hyperbolic RACG acting on its convex core.
---

**ESTABLISHED** by `convex-cores-inherit-greedy-coding-na-proof` (lane `bh-partials`, 2026-09-19; elementary lane
proof, not reviewed; no priority claimed).

## Statement

Let `G` be hyperbolic, acting on a locally finite CAT(0) cube complex `X` cocompactly and freely on vertices, with (NA)
(`greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs`). Let `Q ≤ G` be a non-elementary subgroup with trivial
finite radical, acting cocompactly on a convex subcomplex `Y ⊆ X`. Such a `Y` exists for every quasiconvex `Q`
(Sageev–Wise / Haglund; recalled).

1. The hyperplanes of `Y` are the `H ∩ Y` for the hyperplanes `H` of `X` that meet `Y`, and `H ↦ H ∩ Y` is injective.
2. `H ∩ Y` and `K ∩ Y` cross in `Y` iff `H` and `K` cross in `X`.
3. `(Q, Y)` satisfies (NA).

Hence, by `greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs`, the greedy coding of `∂Y` makes `Q` a faithful
RSG, and a contracting one exactly when it satisfies (IRR).

## Where this leaves Question 1.1 for cubulated groups

- **Hyperbolic ambient.** Quasiconvex subgroups of hyperbolic RACGs, and of any other (NA) cubulation, need only (IRR)
  on their convex cores. That is a finite check once a core is given.
- **Non-hyperbolic ambient.** Virtual specialness (Haglund–Wise, Agol) embeds cubulated hyperbolic groups quasiconvexly
  in right-angled Artin groups. Their Salvetti complexes are not hyperbolic, and (NA) fails there: parallel hyperplanes
  share infinite stabilizers.
- **What is open.** For a general closed hyperbolic 3-manifold group, both (NA) for its own cubulation and (IRR) are
  open. Whether every such group is quasiconvex in some hyperbolic RACG is not settled here.

## Lesson for general BH

- **The geometric half transfers through Helly.** (NA) and the finite nucleus pass to convex cores, because convex
  subcomplexes have Helly number 2. Crossing is therefore detected inside the core, and the core's hyperplane stabilizers
  sit inside the ambient ones.
- **The combinatorial half does not.** Irreducibility belongs to the new coding.
- **So in both directions** (finite-index subgroups, quasiconvex subgroups) the obstruction to Question 1.1 is the same
  single object: the recurrent structure of one finite state graph.

## Attempts

1. **2026-09-19 (lane `bh-q11-beyond`): does the RSG structure restrict along a quasiconvex embedding?** (analysis; one
   small lemma, not reviewed)
   - **Direct restriction fails.** In the RSG structure of the ambient `G` on `∂X`, the canonical similarities between
     same-type cones are realized by elements of `G`, not of `Q`. Restricting to `∂Y` keeps the cones but loses the
     realizing elements. So "contracting RSG" does not pass to subgroups formally; `Q` needs its own coding.
   - **Greedy paths stay in the core (lemma).** Let `v ∈ Y` and `ω ∈ ∂Y`, and let `e` be an edge at `v` dual to a
     hyperplane `H` separating `v` from `ω`. Then the other endpoint `v'` of `e` lies in `Y`.
     - `Y` is the intersection of the halfspaces containing it.
     - A halfspace omitting `v'` but containing `v` is bounded by `H`.
     - `H` meets `Y`, since `Y` has vertices on both sides, so neither halfspace of `H` contains `Y`.

     Hence, with the ambient order restricted to `Y`, the greedy itinerary of `ω` in `Y` is its ambient itinerary. The
     states of `Y`, i.e. an orbit `Qv` together with a set of `Y`-edges at `v`, project onto ambient states, and
     transitions project onto transitions. But transitions that leave `Y` are missing, so `Y`'s state graph is only a
     partial cover of the ambient graph.
   - **For hyperbolic RACG ambients, Lemma K is available at every vertex type.** Since `Y` is convex, each link
     `lk_Y(v)` is a full subcomplex of the nerve `L`, hence flag with no induced 4-cycle. So the minimal-star argument of
     `hyperbolic-racgs-contracting-rsg-via-min-star-order` applies inside each link. Two things are missing:
     - realizability of every simplex of `lk_Y(v)` by a point of `∂Y`: the ray `w_σ(rs)^∞` need not stay in `Y`;
     - a choice of orders across the finitely many vertex types for which the reachability induction closes.
   - **Scope.** Even a full proof here covers quasiconvex subgroups of *hyperbolic* RACGs. Haglund–Wise embed virtually
     special groups quasiconvexly in RAAGs, and in RACGs through C-special complexes, but those ambients need not be
     hyperbolic, and there (NA) can fail. Whether every cubulated hyperbolic group is virtually a quasiconvex subgroup of
     a *hyperbolic* RACG is the bridge this route needs, and it is not settled here.
2. **2026-09-19 (lane `bh-q11-beyond`): the bridge, as a literature question, and the local gap stated precisely.**
   - **Literature: no hyperbolic-ambient version found.** The known embeddings all land in RACGs that need not be
     hyperbolic:
     - Haglund–Wise, *Special cube complexes* (GAFA 2008) and *Coxeter groups are virtually special* (Adv. Math. 2010),
       read as abstract and summary only;
     - the "hyperbolic cubulated ⇒ virtually convex-cocompact in some RACG" statement, as quoted in arXiv:2309.03695;
     - Chesebro–DeBlois–Wilton, arXiv:0903.5288, for right-angled ideal polyhedra.

     Web searches found no statement, positive or negative, that the ambient can be chosen **hyperbolic**. So the bridge
     stays open here:

     > **(Bridge)** Is every hyperbolic, virtually compact special group virtually a quasiconvex subgroup of a
     > *hyperbolic* right-angled Coxeter group?

     If yes, then together with (IRR) for convex cores, Question 1.1 holds for every cubulated hyperbolic group,
     including every closed hyperbolic 3-manifold group (Agol). It covers tautologically the groups commensurable with
     quasiconvex subgroups of hyperbolic RACGs.
   - **The local gap is one thing: backward steps must stay in `Y`.** In the RACG proof, the predecessor
     `P(τ) = {u_1} ∪ (τ ∩ lk(u_1))` is automatically a state: it is the state of the *same* point `ω` seen from the
     neighbour `v'u_1`. Claim A's `ρ` works the same way, one step back along the edge labelled `o`. In the core `Y` both
     backward edges can leave `Y`. So "realizability" and the "cross-type order" reduce to one statement: for every state
     `(v', τ)` of `Y` there is a `Y`-edge at `v'` that plays the role of `u_1`, namely one whose star is minimal in
     `lk_Y(v')`, not in `τ`, and whose far endpoint lies in `Y`. This fails if `v'` is a corner of `Y` where every
     minimal-star edge exits `Y`, so any proof must exploit the choice of core. A thicker convex hull
     (`N_R`-hull) has more edges at each vertex, and that is the natural next attempt.
3. **2026-09-19 (lane `bh-q11-bridge`): the bridge reformulated, and two facts about corners for (L).** (lane proof, not
   reviewed)
   - **The bridge is equivalent to a typing problem.** By `quasiconvex-in-hyperbolic-racgs-iff-square-free-typing`, a
     group is quasiconvex in a hyperbolic RACG iff it acts geometrically, freely on vertices, on a CAT(0) cube complex
     with an invariant hyperplane typing into a finite square-free graph. Square-free vertex links are necessary.
     - The bridge is raised in print by Douba–Fléchelles–Weisman–Zhu (arXiv:2309.03695, §1.2: no known procedure, no
       known obstruction). It is recorded as the
       open node `cubulated-hyperbolic-groups-are-quasiconvex-in-hyperbolic-racgs`.
     - For (L), this means the complex `Y` may be **any** `Q`-cocompact typed complex, not only a core inside one fixed
       ambient.
   - **Corners never go away by thickening.** If `[W : Q] = ∞`, then no `Q`-cocompact convex `Y` equals `Σ`, since `Σ`
     is not `Q`-cocompact. So some vertex of `Y` has an ambient edge leaving `Y`, and its link `lk_Y(v)` is a proper full
     subcomplex of `L`. This holds for every `N_R`-hull.
   - **Links can be cones.** In any convex `Y`, `lk_Y(v)` is the full subcomplex of `L` on the types whose edges at `v`
     stay in `Y`. Taking `Y` to be the intersection of the halfspaces, containing `v`, of the hyperplanes of types
     `O(t) = S ∖ St(t)` at `v` gives `lk_Y(v) = St(t)`, a cone with apex `t`. Lemma K assumes "no cone vertex". So any
     proof of (L) must either choose `Y` to avoid cone links, or handle cone-link vertex types separately, with orders
     chosen per `Q`-orbit of vertices.
   - **Sub-target (L1).** Find a `Q`-cocompact typed `Y` in which no vertex link has a cone vertex. Lemma K then runs
     inside every link. What would remain is the cross-type consistency of the orders. Whether (L1) is always possible is
     open.
4. **2026-09-19 (lane `bh-q11-bridge`): the backward half of the minimal-star argument transfers to typed cores; trees
   satisfy (IRR).** (lane proof, not reviewed)

   Setting: `Q` acts on a typed CAT(0) cube complex `Y`, as in `quasiconvex-in-hyperbolic-racgs-iff-square-free-typing`,
   with links `L_w ⊆ L(Δ)`. The coding is the greedy coding of `greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs`.
   Its statement already allows any `Q`-equivariant order at each vertex, so orders may differ between vertex orbits.
   - **(a) Realized states.** `(v, σ)` is a state iff the sector `{x : the edges at v separating v from x are exactly σ}`
     is infinite.
   - **(b) Backward moves (lemma).**
     - Let `(w, τ)` be a state realized by `ω`, and let `e` be a `Y`-edge at `w` with `e ∉ τ`.
     - Then `ω` has state `P_e(τ) = {e} ∪ (τ ∩ lk(e))` at `we`, by the four-quadrant argument used for the transition
       rule. So `P_e(τ)` is automatically realized.
     - `(we, P_e(τ)) → (w, τ)` is an edge of the state graph iff `e` is the order-minimum of `P_e(τ)` at `we`.
     - Every edge of the state graph arises this way.

     So the "realizability" worry of Attempt 2 disappears for predecessors. A backward step can fail only when the
     needed edge is not a `Y`-edge.
   - **(c) Theorem B (backward half).** Suppose:
     - **(S1)** some type `u` occurs at every vertex of `Y`;
     - **(S2)** at every vertex `w`, each `t ∈ lk_{L_w}(u)` has some `o ∈ L_w ∖ St(u)` not adjacent to `t` (Lemma K's
       conclusion, link by link).

     Order all types globally by `u < V(Δ) ∖ St(u) < lk(u)`. Then every realized state is forward-reachable from a
     realized singleton `({u}, w)`.
     - *Proof.* Claims A and B of `hyperbolic-racgs-contracting-rsg-via-min-star-order`, run as backward moves.
     - (S1) supplies the `u`-edge at every vertex the induction visits. (S2) supplies `o` at the current vertex.
     - (b) makes each predecessor realized, so no sector needs checking.
   - **(d) Cone links block this route.** If `L_w` is a cone with at least 2 vertices, (S2) fails at `w` for every choice
     of `u`. The apex is either `u`, which leaves no candidate `o`, or it lies in `lk(u)` and is adjacent to every
     candidate `o`. So Theorem B needs (L1), except at leaves with `L_w = {u}`.
   - **(e) Trees: (IRR) holds.** If `dim Y = 1`, it holds for every typing and every orders.
     - The states are the directed edges pointing into infinite half-trees.
     - On the minimal subtree `Y_0`, after passing to a torsion-free finite-index subgroup `Q'` (which acts without
       inversions), the state graph is the non-backtracking graph of the finite graph `Y_0/Q'`. That graph has minimum
       degree at least 2 and is not a cycle, so it is irreducible (Hashimoto; recalled). Its image in `Q`'s state graph is
       one strongly connected class.
     - Hair states point toward `Y_0` with strictly decreasing distance, so they lie on no cycle.
     - So there is a single recurrent component. This is a calibration, consistent with virtually free groups being
       contracting RSGs.
   - **(f) What is missing: the forward half.** Every realized state must forward-reach the class of realized
     `{u}`-singletons, and those must be mutually reachable.
     - In the Davis complex this is `σ → σ ∖ {min σ}`.
     - In `Y` that step needs the sector at `v·min σ` with state exactly `σ ∖ {min σ}` to be infinite (**Fill**). It can
       fail at corners.
     - Open, together with realizing (S1), (S2) and (L1) by a choice of `Y` and typing.
