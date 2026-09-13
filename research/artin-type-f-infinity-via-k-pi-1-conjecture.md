---
rg: 2
id: artin-type-f-infinity-via-k-pi-1-conjecture
kind: route
title: The K(π,1) conjecture makes every Artin group of type F, hence of type F_infinity
target: every-artin-group-is-type-f-infinity
requires:
  - artin-group-k-pi-1-conjecture
---

Let `Γ` be a finite Coxeter graph with Coxeter system `(W, S)`.

1. The orbit space `Ω/W` of the complexified hyperplane complement has fundamental group
   `A_W` (van der Lek, 1983).
2. `Ω/W` is homotopy equivalent to the Salvetti complex `Sal(W)`, a CW complex with one
   cell of dimension `|T|` for each subset `T ⊆ S` generating a finite subgroup of `W`
   (M. Salvetti, Math. Res. Lett. 1 (1994); R. Charney and M. W. Davis, 1995). Since
   `S` is finite, `Sal(W)` is a finite complex.
3. If the K(π,1) conjecture holds for `(W, S)`, then `Sal(W)` is a finite `K(A_W, 1)`.
   So `A_W` is of type F, and in particular of type `F_n` for every `n`.

Applying this to every `Γ` gives `every-artin-group-is-type-f-infinity`. Steps 1–2 are
literature inputs cited in the body, not reproved here.
