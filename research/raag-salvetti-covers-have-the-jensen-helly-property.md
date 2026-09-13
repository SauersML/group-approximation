---
rg: 2
id: raag-salvetti-covers-have-the-jensen-helly-property
kind: claim
title: The 1-skeleton of every RAAG Salvetti cover has the Jensen–Helly property of dimension equal to its clique number
---

For every finite simplicial graph `Γ` with maximal clique size `k`, the Cayley
graph of `(A_Γ, V(Γ))` (the 1-skeleton of the universal cover of the Salvetti
complex) has the Jensen–Helly property of dimension `k`, as defined in
`jensen-helly-graphs-have-contractible-rips-complexes`. The natural
realization is the cube complex with the l^1 metric on each cube.

By `every-raag-is-rips-type-r-via-jensen-helly`, this claim answers Zaremsky
Problem 4.5 affirmatively, with `r_0 = k(k+1) − 1`.

## Attempts

- **Products of trees (done).** Complete multipartite `Γ` satisfy it
  (Lemmas J, H, R in
  `research/artifacts/zp-raag-rips-products-of-trees-2026-09-13.md`).
- **(R) holds in general.** A point of a cube is within `k/2` of a corner.
- **(H) through topological Helly.** It suffices that nonempty finite
  intersections of l^1-balls, taken inside a compact contractible subcomplex
  of dimension `k`, are ARs. Then Borsuk's nerve theorem and Čech dimension
  theory run exactly as in Lemma H. Obstacle: l^1-balls are not convex for the
  CAT(0) metric once the complex is not a product. In `Z^2 * Z` a CAT(0)
  geodesic can cross a cut vertex diagonally in one plane and along an axis in
  the next, which makes `d_1(x,·)` concave at the cut point. Candidate repair:
  paths straight in each cube but parametrized by l^1-arclength. For tree-graded
  pieces, `d_1(x,·)` is convex along such paths (left slope ≤ 1 = right slope
  at cut points, checked by hand). Continuity of this bicombing and the
  general cube case are unchecked.
- **(J) is the crux.** In a tree-graded space whose pieces are l^1 planes and
  lines (`Z^2 * Z`), the obvious centre fails: take a piece `A` that no branch
  outweighs, and the mean of the measure projected to `A` through gates.
  Counterexample: mass 1/2 one step behind a cut point `g` and mass 1/2 at
  `y_0 ∈ A` with `d_1(g,y_0) = 10`. The mean in `A` is 5 from `g`. So
  `d(x,b) = 6 > 5.5 = ∫ d(x,y) dμ` for `x` the first point, and the Jensen
  centre must sit at l^1-distance 4.5 from `g`.
  - Sufficient condition, proved by hand: if some piece `A` has every branch
    `β` at `A` with excess moment `M_β = ∫_β d(g_β,y) dμ` at most half of
    `E_A = Σ_β M_β`, then the Jensen centre of the projected measure works.
  - Such pieces need not exist. In the example above the rule oscillates
    between `A` and `g`.
  - Next idea: a hyperplane-wise balance condition generalizing Lemma J's first
    variation, with `b` on the l^1 path that balances first moments across
    every hyperplane adjacent to `b`.
