---
rg: 2
id: fpbs-burnside-normal-closure-split-proof
kind: route
title: Retract onto the remaining generators and bound a finite normal subgroup by a centralizer
target: fpbs-burnside-normal-closure-split
requires:
  - fpbs-burnside-embedding-input
  - fpbs-burnside-nonamenable-two-generator-input
artifacts:
  - research/artifacts/fpbs/docs/normal-subgroup-fixed-price.md
---

Written proof of Lemma 3.1 in Section 3 of the linked note. The retraction
argument uses only relative freeness. Cyclic centralizers of order `n` come
from `fpbs-burnside-embedding-input` (Donoso-Echenique--Silva, Lemma 2.4).
Infinitude of `B(2,n)`, hence of `B(m-1,n)`, follows from the imported Adian
nonamenability. This is not a formal verification.
