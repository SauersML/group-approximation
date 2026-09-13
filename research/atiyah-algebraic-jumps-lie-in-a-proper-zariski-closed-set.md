---
rg: 2
id: atiyah-algebraic-jumps-lie-in-a-proper-zariski-closed-set
kind: claim
title: For a torsion-free group with Strong Atiyah over Qbar, the algebraic points where a two-variable family jumps lie in a proper Zariski-closed set, and the generic rank bounds the kernel everywhere
artifacts:
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed)** by [[atiyah-algebraic-jumps-zariski-closed-proof]].

Let `G` be torsion-free and satisfy Strong Atiyah over `Qbar`, and put
`D = D_(Qbar[G])`. Let `A` be an `m x n` matrix over `Qbar[G][x_1, x_2]`, of
rank `r` over the Ore skew field `D(x_1)(x_2)`.

1. **(Lemma J.)** There is a proper Zariski-closed `Y_A ⊂ A^2` over `Qbar`
   with `dim_G ker A(beta) = n - r` for every `beta in Qbar^2 \ Y_A`. The union
   of its Galois conjugates is a proper closed set over `Q`.
2. **(Lemma L.)** `dim_G ker A(w) >= n - r` for every `w in C^2`.

This is the two-variable analogue of the finiteness of algebraic jump points in
one variable (Theorem 2 of the Liouville artifact).
