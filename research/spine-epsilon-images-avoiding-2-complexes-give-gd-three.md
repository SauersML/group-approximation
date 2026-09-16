---
rg: 2
id: spine-epsilon-images-avoiding-2-complexes-give-gd-three
kind: route
title: If small-fiber images of the spine avoid contractible 2-complexes, the rescaled shadow images force geometric dimension 3 for H_L
target: bestvina-brady-poincare-kernel-has-geometric-dimension-three
requires:
  - spine-epsilon-images-avoid-contractible-2-complexes
  - acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead
artifacts:
  - research/artifacts/eilenberg-ganea-frontier-2026-09-16.md
  - research/artifacts/hl-eg-bestvina-brady-2026-09-14.md
---

This route is a reduction. It replaces the requirement `bestvina-brady-epsilon-map-conjecture` of
`epsilon-map-conjecture-gives-poincare-kernel-gd-three` by the weaker
`spine-epsilon-images-avoid-contractible-2-complexes` (NE). The ε-map conjecture implies NE through
`epsilon-map-conjecture-gives-spine-images-avoid-2-complexes`, and so does Whitehead's conjecture
through TF. Full details are in the artifact, §4.1.

Let `L` be a flag triangulation of the Poincaré-spine, with the unit metric, and `ε` as in NE. Let
`X`, `f` and `X_t` be as in Bestvina--Brady §5 and §8.

**Step 1: bounds.**
- By item 1 of `acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead`, `cd H_L = 2`.
- `X / H_L` is a 3-dimensional `K(H_L, 1)`, so `gd H_L ∈ {2, 3}`.
- Suppose `gd H_L = 2`.

**Step 2: a simplicial model.**
- Take a 2-dimensional CW `K(H_L, 1)`. It is homotopy equivalent to a 2-dimensional simplicial
  complex (recalled standard, not pinned): homotope the attaching maps to edge paths, cone the
  polygons to get a Δ-complex, and take the second barycentric subdivision.
- Its universal cover `Y` is a contractible simplicial 2-complex, with a free deck action of `H_L`.
- As in the proof of Theorem 8.7, take an `H_L`-equivariant PL map `φ: X_t → Y`.

**Step 3: uniform fiber bound.**
- Let `F ⊆ X_t` be compact with `H_L F = X_t`. The deck action is properly discontinuous and `φ(F)`
  is compact, so `T = {h : hφ(F) ∩ φ(F) ≠ ∅}` is finite.
- If `y ∈ h_0 φ(F)`, then `φ^{-1}(y) ⊆ h_0 T F`. So every fiber of `φ` has `X`-diameter at most
  `D = diam(TF)`.
- This is the Bestvina--Brady sentence "point preimages of φ will have diameters bounded", made
  explicit.

**Step 4: rescaled shadows.**
- With `s = |f(v) − t|`, let `σ: L → S_(v,L)` be the homeomorphism. Scaled to side `s`, it is a
  quasi-isometry with constants `λ, c` independent of `s` (Bestvina--Brady, after Definition 8.8,
  as quoted in `epsilon-map-conjecture-gives-poincare-kernel-gd-three`).
- So `g_v = φ ∘ σ: |L| → K_v = φ(S_(v,L))` is a surjective PL map whose fibers have unit-metric
  diameter at most `(λD + c)/s`.
- Choose `v` with `s > (λD + c)/ε`.
- `K_v` is a compact connected subpolyhedron of `Y`. After a subdivision of `Y`, not necessarily
  equivariant, it is a finite subcomplex of the contractible simplicial 2-complex `Y'`.

**Step 5: contradiction.**
- `K_v ⊆ Y'` with the surjective PL map `g_v` of fiber diameters `< ε` contradicts NE.
- Hence `gd H_L = 3`, which is the target.
