---
rg: 2
id: opr-properly-infinite-multiple-splits-citation
kind: route
title: Ortega-Perera-Rordam Theorem 4.3 and Corollary 4.4
target: opr-properly-infinite-multiple-splits
requires: []
---

Source: E. Ortega, F. Perera, M. Rordam, *The Corona Factorization Property
and refinement monoids*, arXiv:0904.0541v1.  Read from the arXiv PDF on
2026-09-12.

Verbatim, Theorem 4.3: "Let M be a conical refinement monoid. Let u be an
order unit such that nu is properly infinite for some n in N. Then there exist
order units s, t in M with u = s + t, and such that ns and nt are properly
infinite."

Verbatim, Corollary 4.4: "Let M be a conical refinement monoid. If u is an
order unit and nu is properly infinite for some n in N, then there is a
sequence t_1, t_2, t_3, ... of order units in M such that
t_1 + t_2 + ... + t_k <= u for all k, and nt_i is properly infinite for all i."

The realization of monoid decompositions by orthogonal subprojections (last
paragraph of the claim) is elementary and not taken from the source: if
`[e] = s + t` in `V(A)`, then `e ~ p direct_sum p'` with `[p] = s`,
`[p'] = t`; conjugating `p direct_sum 0` and `0 direct_sum p'` by the partial
isometry implementing this equivalence gives orthogonal subprojections of `e`
summing to `e` with classes `s` and `t`.  Real rank zero gives refinement of
`V(A)` (Ara--Pardo after Zhang, as recalled on page 3 of the source).
