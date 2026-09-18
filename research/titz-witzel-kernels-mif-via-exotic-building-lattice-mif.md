---
rg: 2
id: titz-witzel-kernels-mif-via-exotic-building-lattice-mif
kind: route
title: The Titz Mite–Witzel kernels are type-preserving free cocompact lattices on thick C̃₂ buildings, so Le Bars–Leibtag–Vigdorovich's theorem makes them MIF
target: titz-witzel-kernels-are-mif
requires:
  - exotic-rank-two-building-lattices-are-mif
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

Fix `i, q`. Write `Γ̌ = Γ̌_i^q ≤ Γ = Γ_i^q` and `X = X_i^q`.

1. **Lattice.** `Γ` acts freely and cocompactly by deck transformations on `X`, a locally finite
   exotic building of type `C̃₂` of thickness `q + 1 ≥ 3`
   (`titz-witzel-simple-kazhdan-cat0-lattices-exist`). `Γ̌` is the finite residual, of finite
   index. So `Γ̌` also acts freely and cocompactly, and it is a cocompact lattice in `Isom(X)`.
2. **Type-preserving.** The type-preserving automorphisms form a finite-index normal subgroup of
   `Aut(X)`, and `Γ̌` is infinite and simple. So `Γ̌` acts type-preservingly. This is step 2 of
   `titz-witzel-kernel-mif-via-opposition-ping-pong`, verbatim.
3. **Apply** item 1 of `exotic-rank-two-building-lattices-are-mif`, in the `C̃₂`, free case. ∎

Credit: Le Bars–Leibtag–Vigdorovich state this application themselves (arXiv:2609.17129, §1.1).
This route only records it in the graph.
