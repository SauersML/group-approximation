---
rg: 2
id: infinite-clique-no-bounded-spin-models-proof
kind: route
title: A Delta-system of supports and pigeonhole on the finite kernel algebra force a nilpotent square
target: infinite-clique-clifford-algebras-have-no-bounded-spin-models
requires: []
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

The proof is Proposition 1.6 of the artifact.

- **Kernel and petals.** Anticommuting elements have meeting supports. An infinite family of supports of
  size at most `d` contains a Delta-system with a nonempty kernel `K` and disjoint petals.
- **Anticommutation moves to `K`.** Independence of petal coefficients on disjoint petals makes the kernel
  coefficient spaces `Pi_x` in `M_K` anticommute elementwise.
- **Pigeonhole.** `M_K` is finite, so two members share `Pi`. Then `Pi` anticommutes with itself, every
  element squares to `0`, and `Pi` generates a nilpotent algebra `N`.
- **Contradiction.** The square of either member lies in `M_(petal) tensor N`, which is nilpotent, but the
  square is invertible.
