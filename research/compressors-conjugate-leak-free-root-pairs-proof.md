---
rg: 2
id: compressors-conjugate-leak-free-root-pairs-proof
kind: route
title: Compute the conjugates on the compressed and complementary summands and read off the leak entries
target: compressors-conjugate-leak-free-root-pairs
requires: []
artifacts:
  - research/artifacts/el3-compressor-root-pair-calculus-2026-09-12.md
---

Artifact Section 1.
* Lemma 1 computes all four conjugates explicitly. `g x g^-1` sends `g(u)` to `g(xu)`. Both
  compressors map two coordinates by left multiplication with `s_0`, and the third onto the
  complement through a fixed isomorphism `R -> R^3`.
* Lemma 2 identifies the leak-free coefficients: `R t_1 t_1` for `c` on the 23 root, and `s_1 R` for
  `c'` on the 12 root, using `t_i s_j = delta_ij` and `s_0 t_0 + s_1 t_1 = 1`.
* Corollary 3 gives the simultaneous conjugacies. Their commutators match the conjugated `x_13`, as
  the homomorphism property requires.
