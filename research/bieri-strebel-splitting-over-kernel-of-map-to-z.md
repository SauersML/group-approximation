---
rg: 2
id: bieri-strebel-splitting-over-kernel-of-map-to-z
kind: claim
title: A finitely presented group mapping onto Z is an HNN extension with finitely generated base inside the kernel
---

**Bieri–Strebel splitting theorem.** Let `G` be finitely presented and `pi: G -> Z`
surjective. Then `G` is isomorphic to an HNN extension `HNN(H, K, L, phi)` whose base `H` is a
finitely generated subgroup of `ker pi`, with associated subgroups `K, L <= H` and
`phi: K -> L` an isomorphism.

Since `H` lies in the kernel, `pi` factors through `G / <<H>> ≅ Z` (the quotient is free on
the stable letter). So the stable letter maps to a generator of `Z`, and
`ker pi = <<H>>`.

Source: R. Bieri and R. Strebel, *Almost finitely presented soluble groups*, Comment. Math.
Helv. 53 (1978). The statement used here is the locally compact version in Y. Cornulier and
P. de la Harpe, *Metric geometry of locally compact groups*, arXiv:1403.3796, §1.F overview of
Chapter 8, specialized to discrete groups (compactly presented = finitely presented).
