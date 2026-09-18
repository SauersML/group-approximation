---
rg: 2
id: closed-surface-groups-contracting-rsg-via-bowen-series
kind: route
title: Code the circle by the Bowen–Series map of the right-angled (8g−4)-gon; canonical similarities are group elements and exactness gives an irreducible core, so what remains is invariance of the cut set and a finite nucleus
target: closed-surface-groups-are-contracting-rsgs
requires:
  - contracting-rsgs-closed-under-finite-index-overgroups
  - sft-irreducible-core-iff-unique-recurrent-component
---

**Status.** Steps 1–3 are proved from the source read. Steps 4 and 5 are OPEN, so the route is OPEN.

**Source read.** Katok–Ugarcovici, *Structure of attractors for boundary maps associated to Fuchsian groups*,
arXiv:1610.00167v2 (Geom. Dedicata 191 (2017)), §1–§2, read as PDF pages 1–9. Stated there:
- `Γ` is a closed genus-`g` surface group with Adler–Flatto's fundamental domain `F`: a regular `(8g−4)`-gon with all
  angles `π/2`.
- Sides `1, …, 8g−4` are paired by `σ(i) = 4g − i` (i odd) and `σ(i) = 2 − i` (i even), with generators `T_i`,
  `T_{σ(i)}T_i = Id`.
- `P_iQ_{i+1}` is the geodesic extending side `i`. The points are in counterclockwise order
  `P_1, Q_1, P_2, Q_2, …, Q_{8g−4}`, and `Π := {P_i, Q_i}`.
- **Prop. 2.2.** `T_i` maps `P_{i−1}, P_i, Q_i, P_{i+1}, Q_{i+1}, Q_{i+2}` to
  `P_{σ(i)+1}, Q_{σ(i)+1}, Q_{σ(i)+2}, P_{σ(i)−1}, P_{σ(i)}, Q_{σ(i)}`.
- **The Bowen–Series map.** `f(x) = T_i x` for `P_i ≤ x < P_{i+1}` (eq. 1.7). It is Markov for the partition `Π`,
  expanding, and satisfies Rényi's distortion estimate. It has a unique finite invariant ergodic measure `μ`
  equivalent to Lebesgue, and it is exact (footnote 1: `F_P̄` is a K-automorphism, which is equivalent to `f` being
  exact).

**Step 1 (the SFT).**
- The states are the `2(8g−4)` arcs `a_i = [P_i, Q_i)` and `b_i = [Q_i, P_{i+1})`.
- Möbius maps preserve the cyclic order, so Prop. 2.2 gives:
  - `T_i(a_i) = [Q_{σ(i)+1}, Q_{σ(i)+2}) = b_{σ(i)+1} ∪ a_{σ(i)+2}`;
  - `T_i(b_i) = [Q_{σ(i)+2}, P_{σ(i)−1}) = b_{σ(i)+2} ∪ a_{σ(i)+3} ∪ b_{σ(i)+3} ∪ ⋯ ∪ b_{σ(i)−2}`.
- So `f` maps each state arc onto a union of state arcs, which is the Markov property made explicit. The transition graph
  `Γ_BS` has an edge `s → t` exactly when `t ⊆ f(s)`.
- **Coding.** Let `B := ⋃_n f^{-n}(Π)`. Cylinders of admissible words are half-open arcs, and `f^n` maps the cylinder
  `[s_0 ⋯ s_n]` onto the arc `s_n` by the Möbius map `g_w := T_{i(s_{n−1})} ⋯ T_{i(s_0)} ∈ Γ`. Here `i(s)` is the
  index `i` with `s ⊆ [P_i, P_{i+1})`.
- `f` is expanding, so cylinders shrink to points. As for β-shifts (`pisot-stein-groups-are-contracting-rsgs-proof`,
  step 1), the itinerary map is an order-preserving homeomorphism from the path space `Σ_{Γ_BS}` onto `S¹_B`, the circle
  Cantorized at `B`.

**Step 2 (RSG property).** Let `[w]` and `[w']` be cylinders with the same last state `s`. Then `g_{w'}^{-1} g_w ∈ Γ` maps
`[w]` onto `[w']`, and on itineraries it is `wω ↦ w'ω`, since `f^{|w|}` sends both to `s·ω`. So every canonical similarity
between cones of the same type is the restriction of a group element. For a root arc `[s]` versus `[w]`, use `g_w^{-1}`.

**Step 3 (irreducible core).**
- Every state arc has positive `μ`-measure, because `μ` is equivalent to Lebesgue. Exactness implies mixing.
- So for states `s, t`, `μ([s] ∩ f^{-n}[t]) > 0` for all large `n`, which gives an admissible path of length `n` from
  `s` to `t`.
- Hence `Γ_BS` is primitive. `Σ_{Γ_BS}` has no isolated points, since it is homeomorphic to `S¹_B`. So its irreducible
  core is all of `Γ_BS` (`sft-irreducible-core-iff-unique-recurrent-component`).

**Step 4 (OPEN: Γ acts on `S¹_B`).**
- **What is needed.** `B` must be `Γ`-invariant. Otherwise some element sends a split point to an unsplit one and is not a
  homeomorphism of `S¹_B`.
- **What holds.** `B ⊆ Γ·Π`. Also `Γ·Π` is the set `W` of endpoints of all walls of the tiling: the walls are the
  complete geodesics formed by edges, and every wall is a translate of a side-wall of `F`.
- **So Step 4 says `W = B`.** Every wall endpoint must reach `Π` under `f`.
- **Why this is plausible.**
  - Tiles beyond `P_iQ_{i+1}` are one step closer to `F` after `T_i`. The dual graph metric counts separating walls, and
    the dual of a right-angled tiling is a CAT(0) square complex.
  - Walls within bounded depth are finitely many, so every wall-endpoint orbit is eventually periodic.
- **Decided by** Bowen–Series orbit equivalence for the orbits of `Π`. That was not read at source: Bowen–Series,
  Publ. IHES 50 (1979).

**Step 5 (OPEN: rational with finite nucleus).**
- **The local actions.** The local action of `h ∈ Γ` at a deep cylinder `[w]` is the group element
  `k = g_v h g_w^{-1}`, where `[v]` is the smallest cylinder containing `h[w]`.
- **What is needed.** For each generator `h`, these `k` lie in one finite set for all but finitely many `w`.
- **The obstacle.** `h[w]` may straddle a shallow cut point, so that `|v| ≪ |w|`. This happens exactly when the level
  defect `level(h·b) − level(b)` is unbounded, where `level(b) = min{n : f^n(b) ∈ Π}`. It is the analogue of step 3 of
  `pisot-stein-groups-are-contracting-rsgs-proof`.
- **The expected mechanism.**
  - The one-sided itineraries of a partition point resynchronize after a bounded delay: KU's cycle property, where the
    upper and lower `f`-orbits of `P_i`, started at `T_iP_i` and `T_{i−1}P_i`, meet.
  - Itineraries are combinatorial geodesic rays in the dual CAT(0) square complex, and their fellow travelling bounds
    `d(g_v^{-1}F, h g_w^{-1}F)`, hence `k`.
- **Warning.** Discreteness alone is not enough. Infinitely many `k ∈ Γ` map a root arc into a root arc with image of
  size `≥ c`. For example, the elements `g u^n`, where `u` generates the stabilizer of a wall whose endpoint is a
  partition point. So the proof must use the cylinder structure.

**Conclusion, once Steps 4–5 hold.**
- `Γ ≤ R_{Γ_BS, Σ}` is an RSG (Step 2), contracting (Steps 3 and 5), and isomorphic to the surface group (faithful on
  `S¹`).
- `contracting-rsgs-closed-under-finite-index-overgroups` then extends this to every group commensurable up from it.
