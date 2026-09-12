---
rg: 2
id: atiyah-counterexample-via-lattice-transfer
kind: route
title: Transfer an irrational L2-Betti number to a torsion-free lattice of the same complex
target: algebraic-strong-atiyah-counterexample-exists
requires:
  - free-cocompact-lattices-proportional-l2-betti
  - complex-with-irrational-and-torsion-free-lattices
artifacts:
  - research/artifacts/atiyah-lattice-transfer-2026-09-12.md
---

## Why sufficient

Take `X`, `G`, `Γ` from `complex-with-irrational-and-torsion-free-lattices`.
- Orient one representative of each `Γ`-orbit of `k`-simplices. The combinatorial
  Laplacian `Δ_k` is then right multiplication by a matrix in `M_(n_k)(Z[Γ])`.
- `dim_(N(Γ)) ker Δ_k = b_k^(2)(X;Γ) = r·b_k^(2)(X;G)`, with `r` rational, by
  `free-cocompact-lattices-proportional-l2-betti`.
- This is irrational, so it is not an integer, and `Γ` is torsion-free.
So `Γ` and `Δ_k` witness `algebraic-strong-atiyah-counterexample-exists`.

## How it differs from the other attempts on the target

The recorded attempts rebuild the lamplighter coins without torsion inside one group:
percolation coins, one-compressor supports, finite spectrum. This route keeps the
torsion group and moves the *value* to a different group through a shared complex. The
cost is geometric: the complex must be non-contractible, have a non-discrete
automorphism group, and carry a torsion-free uniform lattice.
