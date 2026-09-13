---
rg: 2
id: virtually-abelian-groups-rips-via-cat0
kind: route
title: A finitely generated virtually abelian group acts geometrically on Euclidean space, so it has a contractible Rips complex
target: virtually-abelian-groups-have-contractible-rips-complexes
requires:
  - asymptotically-cat0-groups-have-contractible-rips
---

Let `G` be finitely generated with a finite-index subgroup `Z^n`.

1. The intersection of the conjugates of that subgroup is a normal subgroup
   `A ≅ Z^n` of finite index. Put `Q = G/A` and `V = A ⊗ R`, with `Q` acting on `V`
   through conjugation on `A`.
2. The extension `1 → A → G → Q → 1` pushes out along `A → V`. The resulting
   extension of `Q` by `V` splits because `H^2(Q; V) = 0` (`Q` finite, `V` a
   rational vector space). So `G ↪ V ⋊ Q`, and `G` acts on `V` by affine maps
   `(w, q)·x = q x + w`. The linear parts form a finite group `P`, and `A` acts by a
   lattice of translations.
3. Averaging an inner product over `P` gives a `P`-invariant Euclidean structure. `G`
   then acts on the Euclidean space `V` by isometries: properly discontinuously,
   since the finite-index subgroup `A` acts by a lattice of translations, and
   cocompactly, since `V/A` is a torus. For `n = 0`, `V` is a point.
4. Euclidean space is proper, geodesic and CAT(0), hence asymptotically CAT(0). Apply
   `asymptotically-cat0-groups-have-contractible-rips`.
