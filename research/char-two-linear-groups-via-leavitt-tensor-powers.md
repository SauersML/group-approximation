---
rg: 2
id: char-two-linear-groups-via-leavitt-tensor-powers
kind: route
title: Embed transcendence degree d in L^(⊗d) and use the tensor host theorem
target: char-two-linear-groups-satisfy-boone-higman
requires:
  - leavitt-tensor-powers-have-trivial-k-theory
  - leavitt-tensor-hosts-acyclic-steinberg-and-fp
  - central-simple-leavitt-tensor-unit-groups-are-simple
  - char-two-surface-linear-groups-satisfy-boone-higman
artifacts:
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

This is artifact Corollary 7.4.
- **The input.** A finitely generated `H <= GL_n(K)` with entry field of
  transcendence degree `d` lies in `GL_(nm)(F_2[t_1, ..., t_d][1/h])`.
- **The embedding.** Lemma 7.1 embeds that ring unitally in `L^(⊗d)`.
  - The induction step localizes in `t_1, ..., t_(d-1)` at the leading
    coefficient in `t_d`.
  - It realizes the monic localization over `C[g^±]`, and puts `g` in a new
    tensor factor.
  - The step `d = 2` is the proof of `char-two-surface-linear-groups-satisfy-boone-higman`.
- **The host.** `L^(⊗d) = L^(⊗(d-1)) ⊗ L`.
  - Over a field, tensor products of central simple algebras are central
    simple, and tensor products of finitely presented algebras are finitely
    presented.
  - `leavitt-tensor-powers-have-trivial-k-theory` supplies `K_1 = K_2 = 0`.
  - `leavitt-tensor-hosts-acyclic-steinberg-and-fp`(2,3) gives finite
    presentation, and `central-simple-leavitt-tensor-unit-groups-are-simple`(2)
    gives simplicity.
