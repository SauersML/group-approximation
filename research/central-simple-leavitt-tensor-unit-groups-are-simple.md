---
rg: 2
id: central-simple-leavitt-tensor-unit-groups-are-simple
kind: claim
title: For central simple B the elementary groups of B ⊗ L are simple, and so is (B ⊗ L)^x when K_1 and K_2 vanish
distinct_from:
  binary-leavitt-unit-group-is-simple: that is the case B = F_2, the binary Leavitt unit group; this covers every central simple coefficient algebra B, using division in B ⊗ L proved from simplicity of B.
  binary-leavitt-elementary-group-is-simple: that proves simplicity of EL_n over L itself; this proves it over B ⊗ L for every central simple B, by feeding a new division lemma and the centre of the tensor product into the same abstract root-detection theorem.
artifacts:
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

**ESTABLISHED.** Let `B` be a central simple unital `F_2`-algebra, let
`L = L_(F_2)(1,2)`, and put `R = B ⊗ L`.

1. For every `n >= 3`, `E_n(R)` is a simple group.
2. If `K_1(R) = K_2(R) = 0`, then `R^x ≅ GL_3(R) = E_3(R)` is simple, infinite
   and nonabelian.

Part 1 needs no `K`-theory. Consumers:
`leavitt-square-unit-group-is-fp-simple-and-acyclic` and
`boone-higman-via-central-simple-leavitt-tensor-host`.

DERIVATION
central-simple-leavitt-tensor-simplicity-proof
