---
rg: 2
id: degree-one-two-cell-cores-with-ab-nonzero-exist
kind: claim
title: Degree-one two-cell cores with ab != 0 exist, e.g. (a,b) = (1,2) for w = x y^4 x^-1 y^-1 x y^2 x^-1 y^-5 on a 3-vertex graph, so no graph- or homology-level argument forces ab = 0; ratio pairs of w-loops are exactly fiber-product classes with p2 h = lam p1 h, and this example is killed by the character x -> 2, y -> -1
distinct_from:
  two-cell-core-deletions-need-a-unit-fox-coefficient: its searches (length at most 10, at most 3 identifications, random gluings) found no ab != 0 degree-one two-cell core and left their existence open. This constructs one (length 16, 3 vertices), proves that it is a genuine core, and gives an exact criterion that produces such pairs of w-loops.
  core-relation-elimination-bounds-relative-defect: its (E5) shows that torsion-freeness of H_1 allows (a,b) = (1,2) numerically. This realizes (1,2) by an actual core and shows that (E5) and the graph data do not decide admissibility; the row c does.
artifacts:
  - experiments/two-cell-fiber-product-2026-09-18/RESULTS.md
  - experiments/two-cell-fiber-product-2026-09-18/fp.py
  - experiments/two-cell-fiber-product-2026-09-18/words.py
  - experiments/two-cell-fiber-product-2026-09-18/example_check.py
  - experiments/two-cell-fiber-product-2026-09-18/cover3.py
  - experiments/two-cell-fiber-product-2026-09-18/lowindex.g
  - experiments/two-cell-fiber-product-2026-09-18/abel.py
  - experiments/two-cell-fiber-product-2026-09-18/census.py
  - experiments/two-cell-fiber-product-2026-09-18/finchar.py
  - experiments/two-cell-fiber-product-2026-09-18/finchar3.out
  - experiments/two-cell-fiber-product-2026-09-18/gcdfac.py
---

**ESTABLISHED** via `degree-one-two-cell-cores-with-ab-nonzero-exist-proof` (unreviewed). Part (C)
cites three classical theorems:
- Magnus's Freiheitssatz;
- local indicability of torsion-free one-relator groups (Brodskii, Howie);
- the Brodskii–Howie Freiheitssatz for one-relator products of locally indicable groups.

## Setting

The notation is that of `two-cell-core-deletions-need-a-unit-fox-coefficient`:
- `G = ⟨S | w⟩` and `H ≤ G`;
- `C = Γ ∪ e_0 ∪ e_1 ⊂ X_H` is a two-cell core, with `Γ = C^1` a folded `S`-graph;
- `e_j` is the lift of the `w`-cell at the vertex `v_j`, and `z_j ∈ H_1(Γ)` is its boundary cycle;
- the (E5) normal form reads `[u_0] = a p` and `[u_1] = b p`.

## Statement

**(A) Fiber-product criterion.** Let `Γ` be a finite folded `S`-graph and let `λ ∈ Q ∖ {0, 1}`. Let
`Δ` be a component of the fiber product `Γ ×_S Γ` with projections `p_1, p_2`. Then the following
are equivalent.
- Some vertex `(v_0, v_1)` of `Δ` has a nonempty cyclically reduced word `w` that reads closed paths
  at `v_0` and at `v_1` whose cycles satisfy `z_1 = λ z_0 ≠ 0`.
- Some `h ∈ H_1(Δ)` has `p_{2*} h = λ p_{1*} h ≠ 0`.

Every such component is off-diagonal (`v_0 ≠ v_1`), and every such `w` lies in `[F(S), F(S)]`. The
condition is linear algebra over `Q`. Whether `w` is a proper power is checked separately in each
application.

**(B) Explicit example.** Take `S = {x, y}` and
`w = x y^4 x^{-1} y^{-1} x y^2 x^{-1} y^{-5}`. This word is cyclically reduced, is not a proper
power, and lies in `[F,F]`. Let `Γ` have vertices `0, 1, 2` and edges

`x: 0→0, 1→2`,  `y: 0→1, 1→0, 2→2`.

Put `H = ⟨x, y^2, y x y x^{-1} y^{-1}⟩ ≤ G`. Then `w` reads closed loops at `v_0 = 0` and `v_1 = 1`.
Their `B`-words in the basis `a = x`, `b = y^2`, `c = y x y x^{-1} y^{-1}` are

`u_0 = a b^2 a^{-1} b^{-1} c^2 b^{-2}`,  `u_1 = c^4 a b a^{-1} b^{-3}`,

so `[u_0] = p = (0, -1, 2)` and `[u_1] = 2p`. Both cells have degree `+1`, so `ε = 1`,
`(a, b) = (1, 2)`, `b - εa = 1`, the fundamental class is `2e_0 - e_1`, and `H_2(H) → H_2(G)` is onto.
Finally `g = y`.

**(C) It is a genuine core.** `π_1(Γ ∪ e_0 ∪ e_1) → G` is injective. So `C = Γ ∪ e_0 ∪ e_1` is a
degree-one two-cell core of `X_H` with `ab = 2 ≠ 0`. `H` lies in a subgroup `K` of index 3, and `X_K`
is `C` plus one edge and one 2-cell.

**(D) It is not admissible.** Map `x ↦ t` and `y ↦ s`. In the basis `(a, b, c)`, the image of the
cylinder row in `Z[G^ab] = Z[s^{±1}, t^{±1}]` is

`c^ab = f(s) · (s(s-1)(s+1), -(st - s + 1), s + 1)`,  with `f(s) = s^3 - s^2 - 1`. The rational character `χ(x) = 2`,
`χ(y) = -1` has `c^χ = 0`. So `c` is not unimodular over `ZG`, and `pd I_{G/H} ≥ 2` by (U2).

**What this settles.**
- The question "do ab != 0 degree-one two-cell cores exist?", left open by the earlier searches, has
  the answer **yes**.
- So the step "every two-cell core of a degree-one admissible base has ab = 0" cannot be proved from
  the graph, the two `w`-loops, `H_1` or the (E5) normal form. It must use admissibility of the row
  `c` itself. For the constraints that admissibility then imposes, see
  `two-cell-ab-nonzero-admissible-needs-g-in-conj-closure`.

## Evidence beyond the example (not part of the ESTABLISHED statement)

`finchar.py 3` covers every folded graph on 3 vertices, every off-diagonal fiber component and
`λ ∈ {2, 3/2}`, one constructed word each: 132 configurations. All 132 are non-admissible, each with
an exact `F_3`-character certificate. Details are in `RESULTS.md`.

## Attempts

- w9-048 (2026-09-18): the fiber-product criterion, the length-16 example, the core proof via
  Brodskii–Howie, and the character certificate.
