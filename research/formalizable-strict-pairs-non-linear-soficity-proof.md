---
rg: 2
id: formalizable-strict-pairs-non-linear-soficity-proof
kind: route
title: A formal strict pair makes the matrix group algebra not directly finite, which linear soficity forbids
target: formalizable-strict-pairs-certify-non-linear-soficity
requires:
  - formal-polynomial-strict-pairs-need-unstable-linearization
  - linear-sofic-group-algebra-is-stably-finite
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

1. Let `(tau (+) id_k, sigma (+) id_k)` be formalizable on `(F_p^(n+k))^G` with `tau` strict. The
   stabilized `tau (+) id_k` is still strict.
2. By the first prerequisite, if `M_(n+k)(F_p[G])` were directly finite the pair would be bijective. So
   `M_(n+k)(F_p[G])` is not directly finite, and `F_p[G]` is not stably finite.
3. By the second prerequisite, `G` is not `F`-linear sofic for any field `F` containing `F_p`, since a
   one-sided inverse pair in matrices over `F_p[G]` lies over `F[G]` too.
