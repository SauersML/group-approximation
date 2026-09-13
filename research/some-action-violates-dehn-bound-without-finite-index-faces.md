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
