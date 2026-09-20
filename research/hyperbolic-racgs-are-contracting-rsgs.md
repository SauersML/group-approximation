---
rg: 2
id: hyperbolic-racgs-are-contracting-rsgs
kind: claim
title: Every non-elementary hyperbolic right-angled Coxeter group is isomorphic to a contracting RSG, and so is every group commensurable with one
distinct_from:
  hyperbolic-racgs-with-spread-nerves-are-contracting-rsgs: that assumes the spread condition (a) on every simplex of the nerve and a connected complement graph; this drops both, by choosing the order on generators from a vertex of inclusion-minimal star and splitting off cone vertices.
  greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs: that is the conditional theorem with (NA) and (IRR) as hypotheses; this is its unconditional instance for every hyperbolic RACG.
  right-angled-reflection-groups-in-h3-are-contracting-rsgs: that is the H³ right-angled case with face-graph conditions; this covers every hyperbolic RACG in every dimension, with no condition on the nerve.
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that is BBMZ-hyperbolic Question 1.1 for all hyperbolic groups; this answers it for the commensurability classes of hyperbolic RACGs.
---

**ESTABLISHED** by `hyperbolic-racgs-contracting-rsg-via-min-star-order` (lane `bh-q11-beyond`, 2026-09-19; lane
proof, elementary, **not independently reviewed**; no priority claimed). The analytic input is the refereed conditional
theorem `greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs` and Steps 1, 2 and 4 of the refereed
`hyperbolic-racgs-with-spread-nerves-contracting-rsg-proof`. The new part is purely combinatorial.

## Statement

Let `L` be a finite flag simplicial complex with vertex set `S`, and `W = W_L` the right-angled Coxeter group. Suppose
`W` is hyperbolic (`L` has no induced 4-cycle; Moussong) and non-elementary. Then:
1. `W` is isomorphic to a contracting RSG.
2. Every finite-index subgroup of `W`, and every group commensurable with `W`, is isomorphic to a contracting RSG.

Compared with `hyperbolic-racgs-with-spread-nerves-are-contracting-rsgs`, the spread condition (a) and the connectivity
condition (b) are gone.

## How

- **Cone vertices split off.** Let `Δ` be the set of cone vertices of `L` (vertices adjacent to all others). `Δ` is a
  simplex and `L = L_0 ∗ Δ`, so `W = W_{L_0} × (Z/2)^{|Δ|}`. Since `W` is non-elementary, `W_{L_0}` is non-elementary,
  so `|S_0| ≥ 3`, and `L_0` has no cone vertex. Apply `contracting-rsgs-closed-under-products-with-finite-groups`, and
  note that groups commensurable with `W` are commensurable with `W_{L_0}`.
- **Without cone vertices, (b) is automatic.** A disconnected complement graph makes `L` a join, and with no induced
  4-cycle one join factor is a simplex, whose vertices are cone vertices.
- **The order.** Pick `u_1` whose star `St(u_1)` is minimal under inclusion among all vertex stars. Order `S` as
  `u_1 < (S ∖ St(u_1)) < lk(u_1)`, arbitrarily inside the two blocks. For this order, every nonempty simplex is reachable
  from a singleton in the greedy state graph, so the graph is strongly connected. That is (IRR), with no spread condition.
- **The key lemma (uses only "no induced 4-cycle").** For every `t ∈ lk(u_1)` some `o ∉ St(u_1)` is not adjacent to `t`.
  Otherwise a non-neighbour `z` of `t` lies in `lk(u_1)`, has no neighbour outside `St(u_1)` (a neighbour `o` would give
  the induced square `u_1 z o t`), and so `St(z) ⊊ St(u_1)`, against minimality.

## Instances newly covered

- **The hexagon disk.** `L` has vertices `a, b, c_1, c_2, y_1, y_2, x_1, x_2` and triangles
  `abc_1, abc_2, ac_1y_1, bc_1x_1, ac_2y_2, bc_2x_2, ay_1y_2, bx_1x_2`: a flag triangulated disk with boundary hexagon
  `y_1c_1x_1x_2c_2y_2`, no induced square and no cone vertex. `W_L` is one-ended (no separating simplex). The edge `{a,b}`
  and the triangles `{a,b,c_i}` are not spread, so the earlier node does not apply. `St(y_1)` is inclusion-minimal, and the
  order `y_1 < {b, c_2, x_1, x_2} < {a, c_1, y_2}` gives (IRR).
- **Order matters.** In the same example, any order with `c_1, c_2 < a, b <` all other vertices makes
  `{a,b,c_1} ⇄ {a,b,c_2}` a second recurrent component, unreachable from the singletons. So (IRR) is a property of the
  coding, including its order, and not of the group. This repeats the lesson of attempt 6 on Question 1.1.

## What remains of Question 1.1 after this

- **Non-right-angled hyperbolic Coxeter groups**, which are not commensurable with RACGs in general. Their Davis complexes
  are not cube complexes, but Niblo–Reeves cubulate every Coxeter group (recalled), so the greedy coding applies once
  (NA) and (IRR) are checked for that cubulation. That is the natural next target.
- **Virtually special groups that are not commensurable with a RACG**, such as generic closed hyperbolic 3-manifold
  groups: (NA) and (IRR) for their own cubulations, unchanged.
- **Kazhdan hyperbolic groups**, which have no cubulation, unchanged.
