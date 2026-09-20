---
rg: 2
id: typed-core-backward-half-review
kind: claim
title: Referee review of Attempt 4 of convex-cores-inherit-greedy-coding-na (8e6ce89420) — PASS; (b) predecessors are realized by the same boundary point (four-quadrant check), (c) Theorem B's backward induction runs under (S1) and (S2) with the global order u < V∖St(u) < lk(u), (d) cone links with at least two vertices violate (S2) for every u, and (e) typed trees satisfy (IRR) via the non-backtracking graph; the forward half (Fill) is correctly left open
distinct_from:
  convex-cores-inherit-greedy-coding-na: that is the lane node whose Attempt 4 is under review; this checks items (a)–(f) of that attempt.
  hyperbolic-racgs-contracting-rsg-via-min-star-order: that proves Claims A and B in the Davis complex; this checks their transfer to typed cores.
---

**ESTABLISHED (referee bh-ref-e, 2026-09-19; review of Attempt 4 by bh-q11-bridge, landed in 8e6ce89420).** No priority
claimed.
- **Read at source:** Attempt 4 on origin/main, and Steps 1–4 of `hyperbolic-racgs-contracting-rsg-via-min-star-order`.
- **Not re-reviewed:** the wording repairs in the same commit, which apply my review 93f46a050a and match it.
- **No code was run.**

## (b) Predecessors are realized: correct

Let `ω` realize `(w, τ)`, and let `e` be a `Y`-edge at `w` with `e ∉ τ`. Put `w′ = we`.
- **`e` enters the new state.** `H_e` does not separate `w` from `ω`, so it separates `w′` from `ω`.
- **Edges crossing `H_e`.** An edge `f` at `w` with `H_f ⋔ H_e` spans a square with `e`. That square lies in `Y`, by (T2)
  or convexity, so the parallel edge at `w′` is a `Y`-edge. Crossing `H_e` does not change which side of `H_f` we are
  on.
- **Edges at `w′` whose hyperplane `K` misses `H_e`.** Suppose `K` separated `w′` from `ω`.
  - Then `ω ∈ K⁺ ∩ H_e^w`, `w′ ∈ K⁻ ∩ H_e^(w′)` and `w ∈ K⁻ ∩ H_e^w`.
  - The far end of the `K`-edge at `w′` lies in `K⁺ ∩ H_e^(w′)`.
  - So all four quadrants of two disjoint hyperplanes are nonempty, which is impossible.
- **Conclusion.** `ω` has state `P_e(τ) = {e} ∪ (τ ∩ lk(e))` at `w′`.
- **The edge criterion.** `(w′, P_e(τ)) → (w, τ)` is an edge iff `e = min P_e(τ)`, by running the same computation
  forward. Every edge arises this way.

## (c) Theorem B: correct

Use the global order `u < V(Δ) ∖ St(u) < lk(u)`. It is `Q`-equivariant, since types are invariant. Every state is a
simplex of `L_w`: the hyperplanes at `w` that separate `w` from one boundary point pairwise cross.
- **Claim B analogue (`u ∉ τ`).**
  - (S1) gives a `u`-edge at `w`, with `u ∉ τ`.
  - Then `P_u(τ) = {u} ∪ (τ ∩ lk(u))` has minimum `u`, so `(wu, P_u(τ)) → (w, τ)`. It is realized, by (b).
- **Claim A analogue (`u ∈ τ`), by induction on `|τ|`, uniformly over vertices.**
  - `T = τ ∖ {u} ⊆ lk_(L_w)(u)`. For `t ∈ T`, (S2) at `w` gives a type `o ∈ L_w ∖ St(u)` with `o ≁ t`. Its edge is a
    `Y`-edge at `w`, and `o ∉ τ`.
  - `ρ = P_o(τ) = {o} ∪ (T ∩ lk(o))`, using `u ≁ o`, has minimum `o < T`. So `(wo, ρ) → (w, τ)`.
  - `u ∉ ρ`. By (S1) at `wo`, `P_u(ρ) = {u} ∪ (T ∩ lk(o))` gives `(wo·u, P_u(ρ)) → (wo, ρ)`.
  - `|P_u(ρ)| < |τ|`, since `t ∉ lk(o)`, so the induction closes.
- **Every predecessor is realized by the same `ω`.** So no sector needs checking, as the node says.

## (d) Cone links: correct

`(S1)` forces `u ∈ L_w`. Let `L_w` be a cone with apex `c` and at least two vertices.
- **If `c = u`,** then `L_w ∖ St(u) = ∅`, while `lk_(L_w)(u) ≠ ∅`.
- **If `c ≠ u`,** then `c ∈ lk(u)`, and every candidate `o` is adjacent to `c`.

Either way (S2) fails. `L_w = {u}` makes (S2) vacuous.

## (e) Trees satisfy (IRR): correct

- **States.** In a tree, the edges at `v` separating `v` from an end form a single edge. So the states are the directed
  edges pointing into infinite half-trees, and the transitions are non-backtracking.
- **The minimal subtree.** On `Y_0`, choose a torsion-free finite-index `Q′`. It acts freely, without inversions,
  since an inversion would square to an element fixing a vertex.
  - `Y_0/Q′` is a finite graph with no leaves and free fundamental group of rank at least 2, since `Q` is
    non-elementary. So it is not a cycle.
  - Its non-backtracking graph is irreducible. This is recalled, and standard.
  - The `Q`-state graph is a quotient of it, so it is strongly connected on `Y_0`.
- **Hair states.** Edges pointing into finite hairs are unrealized. Hair states pointing toward `Y_0` strictly decrease
  the distance to `Y_0`, so they are transient.
- **Conclusion.** There is exactly one recurrent component.

## (f) The forward half: correctly left open

- **Fill.** "The sector at `v·min σ` with state exactly `σ ∖ {min σ}` is infinite" is what the forward step needs.
  Unlike (b), that state need not be realized by the same `ω`, so it is a genuine additional condition.
- **Other open items.** Realizing (S1), (S2) and (L1) by a choice of `Y` and typing is also open, as stated.

## Verdict

**PASS** for (a)–(e). (f) is correctly marked OPEN. No repairs.
