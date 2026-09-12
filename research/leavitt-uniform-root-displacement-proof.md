---
rg: 2
id: leavitt-uniform-root-displacement-proof
kind: route
title: Bound commutator displacement by twice a factor's and sandwich coefficients to 1
target: leavitt-rank-models-have-uniform-root-displacement
requires:
  - binary-leavitt-algebra-is-purely-infinite-by-monomials
  - binary-leavitt-nonzero-projectives-are-free
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/root-displacement-rank-extraction-2026-09-12.md
---

Section 1 of the artifact.

* **Invariances.** Weyl invariance comes from conjugating by permutation matrices in
  `SL_3(F_2)`; the characteristic is two, so signs vanish. Unit invariance comes from
  `diag(u, v, 1)` in `GL_3(R) = EL_3(R)`.
* **Square-zero bound.** `sigma(x_12(a))^2 = 1` gives `N^2 = 0`, so `rk N <= 1/2`.
* **Product bound.** `[g,h] - 1 = ((g-1)(h-1) - (h-1)(g-1)) g^-1 h^-1` bounds commutator
  displacement by twice either factor's. With `x_13(ab) = [x_12(a), x_23(b)]` this gives the
  product bound.
* **Lower bound.** For `a != 0`, pick monomials with `x a y = 1`. Then
  `x_13(1) = [x_12(x), x_23(ay)]` and `x_23(ay) = [x_21(a), x_13(y)]` give `rho <= 4 rho(a)`.
* **Tuple conjugacy.** Decompose `R^3` along the tuple, and use isomorphisms `e_i R ~= f_i R`
  and `B ~= B'` of nonzero finitely generated projectives. They intertwine every
  `x_12(e_i) - 1` with `x_12(f_i) - 1`.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 37 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
