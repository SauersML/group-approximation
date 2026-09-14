---
rg: 2
id: perfect-group-triangular-model-proof
kind: route
title: Diagonal compression is multiplicative on triangular elements, so the image lies in a nilpotent unipotent group
target: perfect-groups-have-no-triangular-models-with-trivial-diagonal
requires: []
artifacts:
  - research/artifacts/el3-rank-model-extensions-2026-09-12.md
---

Artifact Section 1, Lemma 1.

* **Multiplicativity.** For upper triangular `g, h`, the sum `h_t g h h_t = sum_r (h_t g h_r)(h_r h h_t)`
  has only the `r = t` term. So compression to `h_t M h_t` is multiplicative on the triangular
  subring, and `sigma_t` is a homomorphism.
* **Nilpotency.** If every `sigma_t` is trivial, `sigma(g) - 1` lies in the strictly upper
  triangular part `N`. Let `N_k` be the entries with `r - s >= k`. It is an ideal of the
  triangular ring, `N_k N_l <= N_(k+l)`, and `N_m = 0`. Since
  `[1+x, 1+y] = 1 + (xy - yx)(1+x)^-1(1+y)^-1`, the group `1 + N` is nilpotent of class below
  `m`.
* **Perfection.** `sigma(Gamma)` is a perfect subgroup of a nilpotent group, hence trivial.
