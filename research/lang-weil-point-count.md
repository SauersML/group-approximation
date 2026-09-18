---
rg: 2
id: lang-weil-point-count
kind: claim
title: An affine variety of dimension e defined over F_p has at most C q^e points over F_q, and at least q^e/2 along a geometric sequence of q
---

**ESTABLISHED (literature)** by [[lang-weil-point-count-citation]].

Let `V ⊆ F̄_p^d` be the common zero set of fixed polynomials `P_1..P_m ∈ F_p[X_1..X_d]`, and let `e = dim V`.
For a power `q` of `p`, write `V(F_q) = V ∩ F_q^d`.

1. **(LW-up)** There is `C_V`, independent of `q`, with `|V(F_q)| <= C_V q^e` for every power `q` of `p`.
2. **(LW-low)** If `V` is nonempty, there are `a >= 1` and `j_0` with `|V(F_q)| >= q^e / 2` for all `q = p^{aj}`
   with `j >= j_0`.

This is Corollary 4 of the Lang–Weil bound (Lang–Weil, Amer. J. Math. 76 (1954), MR 65218), in the form stated by
Tao: `|V(F)| = (c(V) + O_M(|F|^{-1/2})) |F|^{dim V}`, where `c(V)` counts the top-dimensional components invariant
under the Frobenius of `F`. For (1), `c(V)` is at most the number of components. For (2), a power of the
`p`-Frobenius fixes every top-dimensional component.
