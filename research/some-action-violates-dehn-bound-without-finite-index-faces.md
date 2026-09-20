---
rg: 2
id: some-action-violates-dehn-bound-without-finite-index-faces
kind: claim
title: "Some cocompact action on a simply connected complex with infinite-index face stabilizers violates the Llosa Isenrich–Weis Dehn function bound"
distinct_from:
  dehn-bound-from-action-data-without-finite-index-faces: that asserts the bound with no hypothesis on face stabilizers; this is its negation.
  cocompact-action-data-do-not-determine-dehn-function: that shows the action data do not determine the Dehn function from below; this asserts that they fail to bound it from above in the stated form.
---

**Statement (open).** There is an action as in
`dehn-bound-from-action-data-without-finite-index-faces` (cellular, cocompact,
without inversions, on a simply connected simplicial complex `X` with finite
`δ_X`, finitely presented vertex stabilizers, finitely generated edge
stabilizers) for which

```text
δ_G(n) is not ≼ δ_X(n) · max_v δ_{G_v}( dist_X‾( δ_X(n) ) ),
```

with `dist_X` the maximum distortion in `G` over stabilizers of cells of
dimension ≤ 2. This answers the upper-bound reading of Zaremsky Problem 1.17
negatively (route `zaremsky-1-17-by-no`).

## Attempts

- A candidate needs face stabilizers of infinite index in their edge
  stabilizers (otherwise Llosa Isenrich–Weis Theorem C applies) and small
  distortion, and must not be product-like, since products of trees are
  expected to satisfy the bound. Triangles of groups with trivial face group
  and large edge groups are the first place to look; the development has to
  stay simply connected with finite `δ_X`.
- 2026-09-13 (`research/artifacts/zp-dehn-cocompact-face-collapse-2026-09-13.md`):
  the uncontrolled cost is the `G`-distance from the loop to the disks over a
  2-cell. A counterexample should have superpolynomial corner
  coarse-intersection function `κ_X` (pairs of edge stabilizers that
  fellow-travel inside a vertex stabilizer far from their intersection) while
  `δ_X`, the vertex Dehn functions and all stabilizer distortions stay
  polynomial. Convex or quasiconvex stabilizers (CAT(0), hyperbolic, Deligne
  complexes of 2-dimensional Artin groups) and products of trees keep `κ_X`
  linear and are ruled out as candidates.
- 2026-09-17 (`research/artifacts/zp-dehn-finite-cluster-collapse-2026-09-17.md`,
  claims `finite-infinite-stabilizer-clusters-give-dehn-bound` and
  `bs1n-actions-satisfy-the-dehn-action-bound`): no counterexample has finite
  clusters. If the union `X_∞` of cells with infinite stabilizer has only
  finite components, then collapsing each to a cone vertex gives a complex
  with finite edge groups. Theorem C applies there and gives (UB), up to an
  inner constant that disappears for doubling vertex Dehn functions or after
  enlarging the generating set.
  - That covers any action whose infinite edge groups have finite index in
    their vertices and whose infinite vertex groups have finite index in their
    commensurators.
  - Every action of `BS(1, q)` satisfies (UB).
  - A counterexample therefore needs an infinite component of `X_∞`, i.e.
    percolating infinite stabilizers, with cluster group `G_C` not virtually a
    vertex group. The triangles of groups with infinite edge groups in the
    first bullet do have this.
