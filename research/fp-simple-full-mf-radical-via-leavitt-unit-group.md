---
rg: 2
id: fp-simple-full-mf-radical-via-leavitt-unit-group
kind: route
title: The binary Leavitt unit group is a finitely presented simple group with full MF radical
target: fp-simple-full-mf-radical-group
requires: [leavitt-unit-group-finitely-presented, binary-leavitt-unit-group-is-simple, binary-leavitt-all-ranks-full-mf-radical]
artifacts:
  - research/artifacts/khanh-2609-08428-leavitt-gl-verified-2026-09-11.md
---

Take `K = L_(F_2)(1,2)^x`.

- `K` is finitely presented: `leavitt-unit-group-finitely-presented`, imported
  from Khanh arXiv:2609.08428v1, Theorem 6.1.
- `K` is simple: `binary-leavitt-unit-group-is-simple`.
- `Rad_MF(K) = K`: `binary-leavitt-all-ranks-full-mf-radical`, which covers the
  unit group and every `GL_n(L)`.

So `K` witnesses `(FPS1)` of the target. The finite-presentation input is a v1
preprint whose proof has not been reviewed in this repository; see the artifact.
