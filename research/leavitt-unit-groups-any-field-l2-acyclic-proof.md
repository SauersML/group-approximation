---
rg: 2
id: leavitt-unit-groups-any-field-l2-acyclic-proof
kind: route
title: Leavitt word reduction with a nonzero scalar leading coefficient, then the frame criterion
target: leavitt-unit-groups-over-every-field-are-l2-acyclic
requires: [frame-acyclic-rings-have-low-degree-l2-acyclic-gl, binary-leavitt-frame-complexes-are-highly-acyclic]
artifacts:
  - research/artifacts/leavitt-unit-l2-acyclicity-any-field-2026-09-12.md
---

Artifact Sections 1--3.
- **Lemma 4.1 over `K`.** Khanh's word reduction produces `x` and words `η_i` with
  `η_i* a_i x = c_i in K^x`. Put `b_i = c_i^(-1) η_i*`, which has the same kernel
  `⊕_ℓ s_ℓ S`.
- **Proposition 4.2 and Corollary 4.3** use `b_i` only through `b_i y_i = 1` and that kernel,
  so they transfer. Hence `X_r(L_K(1,2))` is `(r-3)`-acyclic. The F_2 import
  `binary-leavitt-frame-complexes-are-highly-acyclic` is the template whose proof is rerun.
- **Frame criterion** at `r = n+3`, then `GL_r(S) ≅ S^x` by prefix codes.
