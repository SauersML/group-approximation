---
rg: 2
id: tile-two-graph-affine-corners-proof
kind: route
title: Read the far label of each corner edge as an affine point or line, and reduce square completion to incidence via (A2)–(A3)
target: triangle-presentation-tile-two-graphs-have-affine-corner-graphs
requires: []
artifacts:
  - research/artifacts/nv-brick-coding-corner-kill-2026-09-17.md
  - experiments/nv-kazhdan-independence-2026-09-17/corners_all.py
  - experiments/nv-kazhdan-independence-2026-09-17/corners_all.log
---

Full proof: Part F (F0–F4) of the artifact. It is self-contained. It uses only (A1)–(A3),
(H1) and the incidence axioms of a projective plane. Notation: `I(x,y)` means
`y ∈ λ(x)`, and `τ(x,y)` is the third entry of the triple. `x'`, `u'`, … are the labels of
`b`, and `y''`, `w''`, … are the labels of `c`.

1. **F0.** `(y,u,w) ∈ T` gives `w ∈ λ(u)`.
2. **F1 (colour 1).**
   - Write `b = (x',y',w,u',w')`, so `y' = τ(w,x')`.
   - `x' ↦ y'` is a bijection onto the `p` with `w ∈ λ(p)`, and `x' = y` iff `y' = u`.
   - Both `u'` and `w` lie on `λ(y')`, so `λ(y') = wu'`.
   - Hence `b ↦ u'` is injective, and `u' ∉ ℓ`.
   - Conversely, every `p ∉ ℓ` arises, with `λ(y') = wp`.
3. **F2 (colour 2).**
   - Write `c = (u,y'',z'',u'',w'')`.
   - `w'' = u` iff `u'' = z''`, so `λ(w'') ≠ ℓ`.
   - `λ(w'') ∩ ℓ = {y''}` recovers `c`, and `w ∉ λ(w'')` since `y'' ≠ w`.
   - Every line not through `w` arises.
4. **F3 (compatibility).**
   - A common successor `d = (u',Y,w'',U,W)` exists iff `I(w'',u')`, `u' ≠ y''` and
     `w'' ≠ y'`.
   - Here `Y = τ(w'',u')`. By (A2)–(A3), `Y = w'` iff `w'' = y'`.
   - The last two conditions are automatic under F1 and F2.
   - (H1) makes `c` the unique filling of `a→b→d`, so `d` exists iff the square exists.
5. **F4 (connectivity).**
   - Two affine points are joined by their line if it misses `w`.
   - Otherwise they are joined through any affine point off that line, in two steps.
   - Every allowed line has `q` affine points.

Computational check: `corners_all.py` confirms connectivity, degrees `q`, and at most one
common neighbour at every vertex, for the five `PG(2,2)` and two `PG(2,3)` presentations.
The log is `corners_all.log`.
