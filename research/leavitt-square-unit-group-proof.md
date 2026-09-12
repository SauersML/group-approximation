---
rg: 2
id: leavitt-square-unit-group-proof
kind: route
title: Take B = L in the tensor host theorem, with K-theory from Ara--Cortiñas
target: leavitt-square-unit-group-is-fp-simple-and-acyclic
requires:
  - ara-cortinas-leavitt-tensor-k-theory-vanishes
  - leavitt-tensor-hosts-acyclic-steinberg-and-fp
  - central-simple-leavitt-tensor-unit-groups-are-simple
  - leavitt-center-is-coefficient-field
artifacts:
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

Take `B = L` (artifact Theorem 6.1).

1. **`B` is central simple.** `L` is simple (the division property, artifact
   Corollary 2.3 with coefficient algebra `F_2`), and its centre is `F_2` by
   `leavitt-center-is-coefficient-field`.
2. **`B` is finitely presented.** It is a finitely presented ring by Khanh's
   relators (6.1): `2, se-1, tf-1, sf, te, es+ft-1`. So `L ⊗ L` is presented by
   two copies of these six relators and the sixteen commutators between the
   two alphabets.
3. **`K`-theory.** `ara-cortinas-leavitt-tensor-k-theory-vanishes` gives
   `K_i(L ⊗ L) = 0` for every `i`.
4. **Conclusion.**
   - `leavitt-tensor-hosts-acyclic-steinberg-and-fp`(1) gives integral
     acyclicity.
   - Its part (2) gives the Steinberg isomorphism.
   - Its part (3) gives finite presentation.
   - `central-simple-leavitt-tensor-unit-groups-are-simple`(2) gives simplicity.
