---
rg: 2
id: kazhdan-boone-higman-via-central-simple-leavitt-tensor-host
kind: route
title: The central simple Leavitt tensor unit group host is Kazhdan, so the Boone--Higman ring premise already gives Kazhdan Boone--Higman
target: kazhdan-boone-higman-conjecture
requires:
  - decidable-group-algebras-have-fp-central-simple-hosts
  - leavitt-tensor-hosts-acyclic-steinberg-and-fp
  - central-simple-leavitt-tensor-unit-groups-are-simple
  - ring-elementary-bh-hosts-are-kazhdan
artifacts:
  - research/artifacts/ring-hosts-are-kazhdan-2026-09-17.md
---

Let `G` be finitely generated with solvable word problem. Take `B` from
`decidable-group-algebras-have-fp-central-simple-hosts`, and put
`R = B ⊗ L_(F_2)(1,2)`.

1. **Embedding, finite presentation, simplicity.** These are the steps of
   `boone-higman-via-central-simple-leavitt-tensor-host`:
   - `G <= R^x`;
   - `R^x` is finitely presented by
     `leavitt-tensor-hosts-acyclic-steinberg-and-fp`(3);
   - `R^x` is simple by
     `central-simple-leavitt-tensor-unit-groups-are-simple`(2).
2. **(T).** `B` is central simple and `K_1(R) = K_2(R) = 0`. So
   `ring-elementary-bh-hosts-are-kazhdan`(3) says that `R^x` has property (T).

Hence `G` embeds in a finitely presented simple group with (T). With
`ck-finite-bi-index-hole-via-kazhdan-boone-higman`, the same premises give the
free-core reading of `ck-envelope-simple-core-has-finite-bi-index`.
