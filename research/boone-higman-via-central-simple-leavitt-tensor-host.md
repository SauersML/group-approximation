---
rg: 2
id: boone-higman-via-central-simple-leavitt-tensor-host
kind: route
title: Put the group algebra in a finitely presented central simple algebra and take the unit group of its Leavitt tensor
target: boone-higman-conjecture
requires:
  - decidable-group-algebras-have-fp-central-simple-hosts
  - leavitt-tensor-hosts-acyclic-steinberg-and-fp
  - central-simple-leavitt-tensor-unit-groups-are-simple
artifacts:
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

Let `G` be finitely generated with solvable word problem, and take `B` from
`decidable-group-algebras-have-fp-central-simple-hosts`. Put
`R = B ⊗ L_(F_2)(1,2)`.

1. `G <= F_2[G]^x <= B^x <= R^x`, through `b |-> b ⊗ 1`. This is injective
   because tensor products over a field are faithful.
2. `K_1(R) = K_2(R) = 0` and `B` is finitely presented, so
   `leavitt-tensor-hosts-acyclic-steinberg-and-fp`(3) makes `R^x` finitely
   presented.
3. `B` is central simple, so
   `central-simple-leavitt-tensor-unit-groups-are-simple`(2) makes `R^x`
   simple.

Hence `G` embeds in a finitely presented simple group.

**What this route removes.** The old ring route
`boone-higman-via-projective-ring-host` needs finite normal generation of an
unstable Steinberg kernel over an arbitrary host. Here that kernel is trivial
by Khanh's comparison criterion, as soon as `K_1` and `K_2` of `R` vanish. What
remains is an existence problem for algebras, and nothing about normal
subgroups.
