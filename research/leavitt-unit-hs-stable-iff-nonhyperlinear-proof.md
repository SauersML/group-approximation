---
rg: 2
id: leavitt-unit-hs-stable-iff-nonhyperlinear-proof
kind: route
title: Lift through the finite presentation and kill the lifts by minimal almost periodicity
target: leavitt-unit-hs-stable-iff-nonhyperlinear
requires: [leavitt-unit-group-finitely-presented, binary-leavitt-unit-group-is-simple, binary-leavitt-unit-group-is-minimally-almost-periodic, leavitt-steinberg-map-iso-from-rank-three, leavitt-gl-equals-el-and-perfect-unit-group]
---

The four-step derivation is written in the body of the target.
* Finite presentation turns vanishing relator defects into a homomorphism
  into a tracial matrix ultraproduct, and back.
* Simplicity makes every nontrivial such homomorphism injective.
* Minimal almost periodicity makes the only exact representations trivial, so
  "close to a representation" means "close to 1".
* Khanh's Steinberg comparison, `GL = EL`, and the prefix-code isomorphisms
  `M_k(L) = L` identify `St_5(L)` and `EL_4(L)` with `L^x`.
