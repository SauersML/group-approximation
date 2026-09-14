---
rg: 2
id: lot-asphericity-via-whitehead-conjecture
kind: route
title: The Whitehead conjecture makes every LOT complex aspherical, because LOT complexes sit inside contractible 2-complexes
target: labeled-oriented-trees-are-aspherical
requires: [whitehead-asphericity-conjecture]
---

Let `Γ` be a LOT with vertices `x_1, ..., x_n` and `n - 1` edges, and let
`K = K(Γ)` be the standard 2-complex of its LOT presentation.

**Step 1: all generators are conjugate.** An edge `[s, l, t]` gives the relation
`s l = l t`, so `t = l^-1 s l` in `G(Γ) = π_1(K)`. The underlying graph is a
tree, hence connected, so every generator is conjugate to `x_1`.

**Step 2: a contractible overcomplex.** Let `L = K ∪ e^2`, attaching one 2-cell
along the loop `x_1`. Then `π_1(L) = G(Γ)/<<x_1>>`, and by Step 1 every
generator lies in `<<x_1>>`, so `π_1(L) = 1` and `H_1(L) = 0`. `L` has one
0-cell, `n` 1-cells and `(n - 1) + 1 = n` 2-cells, so `χ(L) = 1`. Since `L` is
2-dimensional, `χ(L) = 1 - rank H_1(L) + rank H_2(L)`, and `H_2(L)` is free
abelian, so `H_2(L) = 0`. By Hurewicz `π_2(L) = H_2(L) = 0`; a simply connected
2-complex with `H_2 = 0` has all homology of its (trivial) universal cover
vanishing, so `L` is contractible by Whitehead's theorem.

**Step 3.** `K` is a connected subcomplex of the aspherical (indeed contractible)
2-complex `L`. `whitehead-asphericity-conjecture` gives that `K` is aspherical.

Elementary; the same observation for Wirtinger presentations is stated at
arXiv:1212.1943 l.98 ("The Wirtinger presentation of a knot gives rise to a
2-complex that is a subcomplex of a contractible 2-complex").
