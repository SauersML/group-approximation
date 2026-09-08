---
rg: 2
id: jacobson-shift-coordinate-extension-induction-proof
kind: route
title: Use compatible four-coordinate seeds to extend packets and then centralize distant intervals
target: jacobson-shift-has-full-finite-linear-intervals
requires:
  - jacobson-stable-letter-closes-boundary-recursion
  - jacobson-shift-exact-representations-kill-head
artifacts:
  - research/artifacts/jacobson-recursive-packets-generate-finitary-linear-kernel-2026-09-08.md
---

The first prerequisite fixes the finite packets, their embeddings and
the seven exact shifts; the second supplies head centralization of
the next compressed subgroup. The proof artifact uses that algebraic
centralization calculation, not its finite-dimensional conclusion.

Given `GL(U+z),GL(U+w)` agreeing on `GL(U)`, a matching seed
`GL(U_0+z+w)` with two-coordinate `U_0` supplies every missing
root relation. Its `z,w` roots centralize `GL(U)` by writing them
as commutators through either seed coordinate; remaining pair relations
transport into the seed. The finite Steinberg presentation yields the
larger group, and the literal action makes it faithful.

The shifted boundary verifies the seed embeddings needed to join
`K_i,K_(i+1)` into `GL_9`. Commutation of their pure swaps then
implies `K_i` centralizes all three generators of `Theta_(i+2)`.
For interval induction, a swap from the next packet centralizes the
entire old group omitting its one moved coordinate: this follows from
distant packet commutation and the already authenticated adjacent
`GL_9`. Repeated coordinate extensions add the next full level.
Sections 2--5 verify all overlapping root identifications explicitly.
