---
rg: 2
id: elementary-leavitt-hosts-from-central-simple-hosts
kind: route
title: The K-theoretically trivial host premise gives the elementary host premise with trivial Steinberg kernel
target: simple-inputs-have-fp-elementary-leavitt-tensor-hosts
requires:
  - decidable-group-algebras-have-fp-central-simple-hosts
  - leavitt-tensor-hosts-acyclic-steinberg-and-fp
  - boone-higman-thompson-simple-envelope
artifacts:
  - research/artifacts/bh-decidable-algebra-hosts-2026-09-12.md
---

This route records that the new premise is implied by the old one. It is
therefore at most as hard, and the elementary-host formulation loses nothing.

Let `S` be infinite, finitely generated, computably presented and simple.

1. **`S` has solvable word problem.** `S` embeds in itself, a finitely generated
   computably presented simple group, so by `boone-higman-thompson-simple-envelope`
   its word problem is solvable.
2. **Take the old host.** `decidable-group-algebras-have-fp-central-simple-hosts`
   gives a finitely presented central simple `B` with a unital embedding
   `F_2[S] -> B` and `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`. Restricting to the group
   elements gives an injective homomorphism `S -> B^x`.
3. **The kernel is trivial.** By `leavitt-tensor-hosts-acyclic-steinberg-and-fp`
   (2), `GL_m(B ⊗ L) = E_m(B ⊗ L)` for `m >= 2`, and `St_r(B ⊗ L) -> GL_r(B ⊗ L)`
   is an isomorphism for `r >= 3`. So for `n = 4` the map `St_4 -> E_4` is an
   isomorphism, and its kernel is trivial, hence finitely normally generated.
