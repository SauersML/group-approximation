---
rg: 2
id: artin-groups-of-rank-at-most-four-satisfy-k-pi-1-proof
kind: route
title: Rank at most four is spherical or of dimension at most three
target: artin-groups-of-rank-at-most-four-satisfy-k-pi-1
requires:
  - spherical-artin-groups-satisfy-k-pi-1-conjecture
  - commutation-4-cycle-free-artin-groups-satisfy-k-pi-1
---

Let `Γ` be a Coxeter graph on `S` with `|S| ≤ 4`.

1. If `W_Γ` is finite, `A_Γ` satisfies the K(π,1) conjecture by
   `spherical-artin-groups-satisfy-k-pi-1-conjecture`.
2. If `W_Γ` is infinite, then no `T ⊆ S` with `|T| ≥ 4` generates a finite subgroup, because
   the only such `T` is `S` itself. So `A_Γ` has dimension at most 3, and
   `commutation-4-cycle-free-artin-groups-satisfy-k-pi-1` applies. Infinite labels are
   allowed there, since its Coxeter diagrams carry labels `3, …, ∞`.

For type F: the Salvetti complex of `Γ` is a finite CW complex homotopy equivalent to the
orbit space of the complexified hyperplane complement (M. Salvetti, Math. Res. Lett. 1 (1994),
cited in arXiv:1907.11795 for "a classifying space with a finite number of cells"). When that
space is aspherical, the Salvetti complex is a finite `K(A_Γ, 1)`.
