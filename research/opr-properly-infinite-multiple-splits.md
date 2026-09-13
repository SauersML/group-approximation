---
rg: 2
id: opr-properly-infinite-multiple-splits
kind: claim
title: An order unit with a properly infinite multiple splits into infinitely many pieces whose multiples stay properly infinite (OPR Theorem 4.3)
---

**Theorem (Ortega--Perera--Rordam, arXiv:0904.0541, Theorem 4.3 and
Corollary 4.4).**  Let `M` be a conical refinement monoid and `u in M` an
order unit such that `n u` is properly infinite for some `n in N`.

1. There are order units `s,t in M` with `u = s + t` such that `n s` and
   `n t` are properly infinite.
2. There is a sequence `t_1, t_2, ...` of order units with
   `t_1 + ... + t_k <= u` for every `k` and `n t_i` properly infinite for
   every `i`.

Here `x` is properly infinite when `2x <= x`, and `x <= y` is the algebraic
order (`x + z = y` for some `z`).  The proof first shows that a monoid with a
properly infinite order unit has weak divisibility for order units
(Proposition 2.10), so the order units together with `0` form a simple
refinement monoid (Theorem 3.4), and then refines `n u = n u + v` against the
row `u, ..., u` (Proposition 4.2).

For a C\*-algebra `A` of real rank zero, `V(A)` is a conical refinement monoid,
and a decomposition `[e] = s + t` of the class of a projection is realized by
orthogonal subprojections of `e`.  Iterating part 1 therefore produces, inside
any projection `e` with `n[e]` properly infinite and `[e]` full, an infinite
orthogonal sequence of nonzero subprojections `e_i` with every `n[e_i]`
properly infinite.
