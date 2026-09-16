---
rg: 2
id: epsilon-map-conjecture-gives-spine-images-avoid-2-complexes
kind: route
title: A cell-attachment model for a small-fiber image transports the spine into a contractible 2-complex, which claim A forbids
target: spine-epsilon-images-avoid-contractible-2-complexes
requires:
  - bestvina-brady-epsilon-map-conjecture
  - acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear
artifacts:
  - research/artifacts/eilenberg-ganea-frontier-2026-09-16.md
---

This is Steps 3--5 of `epsilon-map-conjecture-gives-poincare-kernel-gd-three`, stated for an
arbitrary small-fiber image instead of a shadow image. See the artifact, §4.2.

Let `L` be the flag triangulation of the Poincaré-spine with the unit metric. Let `ε_0` be the
constant of `bestvina-brady-epsilon-map-conjecture` for this metric. We show NE with `ε = ε_0`.

**Step 1: setup.** Suppose `Y` is a contractible simplicial 2-complex, `K ⊆ Y` a finite subcomplex,
and `g: |L| → |K|` a surjective PL map with fibers of diameter `< ε_0`.

**Step 2: weak form (E).**
- By the conjecture, `K` is homotopy equivalent to `M = L ∪ (1-cells) ∪ (2-cells)`, a
  2-dimensional CW complex containing `L` as a subcomplex.
- Choose a cellular homotopy equivalence `h: K → M`.

**Step 3: transport.**
- Let `Z = M ∪_h Y` be the pushout of `M ←h− K ↪ Y`.
- The inclusion of a subcomplex is a cofibration, and `h` is a homotopy equivalence. By the gluing
  theorem for adjunction spaces (recalled standard, not pinned), `Y → Z` is a homotopy equivalence.
  So `Z` is contractible.
- `h` is cellular, so `Z` is a 2-dimensional CW complex containing `M`, and hence `L`, as a
  subcomplex.

**Step 4: contradiction.**
- `L` is a finite subcomplex of `Z` with `H_1(L; Z) = 0`.
- `π_1(L) = SL(2,5)` is finite and nontrivial, hence hyperlinear.
- This contradicts `acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear`. So no such
  `(Y, K, g)` exists.
