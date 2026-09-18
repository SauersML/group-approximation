---
rg: 2
id: titz-witzel-lattices-pbh-via-euclidean-building-lattices
kind: route
title: The Titz Mite–Witzel lattices are uniform lattices on locally finite thick C̃₂ buildings, so the Euclidean building lattice theorem puts them in B_A
target: titz-witzel-lattices-satisfy-permutational-boone-higman
requires:
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
  - euclidean-building-lattices-lie-in-permutational-bh-class
---

1. By `titz-witzel-simple-kazhdan-cat0-lattices-exist` (Titz Mite–Witzel, Theorem A),
   `Γ_i^q = π_1(Y_i^q)` acts freely and cocompactly by deck transformations on the universal
   cover `X_i^q`. This cover is an exotic building of type C̃₂ with thickness `q + 1`, where
   `q = 2, 3`. So `X_i^q` is a locally finite thick irreducible Euclidean building, and
   `Γ_i^q ≤ Aut(X_i^q)` is discrete and cocompact.
2. By `euclidean-building-lattices-lie-in-permutational-bh-class`, `Γ_i^q ∈ B_A`. That node
   lists these lattices among its new cases.
3. `B_A` is closed under subgroups. So the simple kernels `Γ̌_i^q` are in `B_A` as well.

This is graph wiring by bh-integrate (2026-09-18). It adds no mathematics beyond checking that
the hypotheses match. The claim rests on bh-groupoid's lane proof, which has not been
independently reviewed. The older route `titz-witzel-lattices-pbh-from-mif-kernels` still
reduces the claim to `titz-witzel-kernels-are-mif`, which stays OPEN.
