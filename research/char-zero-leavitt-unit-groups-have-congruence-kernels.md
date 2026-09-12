---
rg: 2
id: char-zero-leavitt-unit-groups-have-congruence-kernels
kind: claim
title: Unit groups of binary Leavitt algebras over finitely generated characteristic-zero domains are not simple
distinct_from:
  binary-leavitt-unit-group-is-simple: that is simplicity over F_2; this shows the characteristic-zero analogue fails, by reduction modulo a finite residue field.
  leavitt-tensor-hosts-acyclic-steinberg-and-fp: that transfers Khanh's finite presentation and acyclicity to tensor hosts over finite prime fields; this records that the direct characteristic-zero host is not even simple.
  affine-self-similar-coordinate-rings-are-one-dimensional: that obstructs affine self-similar hosts at positive transcendence degree; this obstructs Leavitt unit groups over characteristic-zero coefficient rings.
---

**ESTABLISHED.** Let `A` be a finitely generated commutative ring that is a
domain of characteristic zero, and let `L_A = L_A(1,2)`. Then `L_A^x` has a
normal subgroup `N` with `1 != N != L_A^x`. So `L_A^x` is not simple.

**Consequence for Boone--Higman.** The Leavitt hosts of
`positive-char-surface-linear-groups-satisfy-boone-higman` have no direct
characteristic-zero version:
- **Over finitely generated domains:** the unit group of `L_Z(1,2)`, or of
  `L_A(1,2)` for any finitely generated characteristic-zero domain `A`, has a
  congruence kernel.
- **Over characteristic-zero fields `K`:** the central scalars `K^x` already
  prevent simplicity. Passing to the quotient by them loses the scalar actions
  of finite multiplicative groups that Khanh's acyclicity and Steinberg
  comparison use.
