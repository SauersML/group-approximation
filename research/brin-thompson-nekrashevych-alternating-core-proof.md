---
rg: 2
id: brin-thompson-nekrashevych-alternating-core-proof
kind: route
title: The groupoid of germs of nV_d(H) is an effective minimal Cantor groupoid whose full group is nV_d(H) itself, so Nekrashevych's Theorem 1.1 applies
target: brin-thompson-nekrashevych-groups-have-simple-alternating-core
requires: []
---

Notation is as in the target. The unit space `(X^ω)^n` is a Cantor space, and
`G_H` is the groupoid of germs of an action, which is étale
(arXiv:1511.08241v2, Example 2.2 and the remark after Definition 2.1).

**Step 1 (groupoid of germs).**
- Take a non-unit germ `γ = (g, x)` and a bisection `F ∋ γ`. A bisection
  containing `γ` contains all germs `(g, y)` for `y` in some neighborhood `U`
  of `x`.
- Since `γ` is not a unit, `g` is not the identity on any neighborhood of `x`,
  so some `y ∈ U` has `g(y) ≠ y`.
- Then `δ = (g, y) ∈ F` has `s(δ) = y ≠ g(y) = r(δ)`. So `G_H` is a groupoid of
  germs in the sense of Definition 2.2.

**Step 2 (minimal).**
- Let `x ∈ (X^ω)^n`, and let `β` be any brick. Choose a brick `β_0 ∋ x`. Some
  table partitions the cube with `β_0` among its domain bricks and `β` among
  its range bricks: refine `β_0` and `β` into two partitions with the same
  number of bricks.
- The corresponding element of `nV ≤ nV_d(H)` maps `x` into `β`. So every
  orbit is dense.

**Step 3 (full group).**
- **Full group to `nV_d(H)`.** Let `F` be a bisection with `s(F) = r(F)` the
  whole space. Each point of `F` lies in a basic bisection
  `{(g, y) : y ∈ U}` with `g ∈ nV_d(H)` and `U` a brick. By compactness,
  finitely many such pieces with disjoint sources cover `F`: pairs
  `(g_i, U_i)`, where the `U_i` partition the cube and the images `g_i(U_i)`
  partition it too.
  - Refine each `U_i` so that every piece lies in one table brick of `g_i`.
  - On such a piece `g_i` acts by a decorated brick map, and the pieces with
    their images form a decorated table.
  - So the associated homeomorphism lies in `nV_d(H)`.
- **`nV_d(H)` to full group.** Every `g ∈ nV_d(H)` gives the bisection of its
  germs at all points.
- **Matching.** Because `G_H` is a groupoid of germs, the two definitions of
  the full group agree (remark after Definition 2.3). So the full group of
  `G_H` is `nV_d(H)`.

**Step 4.** By Steps 1 and 2, Theorem 1.1 of arXiv:1511.08241v2 applies to
`G_H`, and by Step 3 its full group is `nV_d(H)`. ∎
