---
rg: 2
id: algebraic-dependence-from-finite-centralizer-rank
kind: route
title: A finite-dimensional localized centralizer makes every commuting unit algebraic over the Laurent ring of the first
target: leavitt-commuting-units-are-algebraically-dependent
requires: [leavitt-unit-centralizers-have-finite-rank]
---

Let `a, c` be commuting units of `R = L_(F_2)(1,2)`.

1. If `c` has finite order `m`, then `P = y^m - 1` gives `P(a, c) = 0`. So assume `c` has infinite order, and
   put `C = C_R(c)` and `S = F_2[c] - {0}`.
2. By `leavitt-unit-centralizers-have-finite-rank`, `n = dim_(F_2(c)) S^(-1) C` is finite. The `n + 1` elements
   `1, a, ..., a^n` of `S^(-1) C` are therefore linearly dependent over `F_2(c)`.
3. Clearing denominators gives polynomials `q_0, ..., q_n`, not all zero, such that `sum_i q_i(c) a^i` is killed
   in `S^(-1) C`. So some `s(c)` in `S` satisfies `s(c) sum_i q_i(c) a^i = 0` in `C`.
4. `P(x, y) = s(y) sum_i q_i(y) x^i` is a nonzero polynomial, because `F_2[x, y]` is a domain, and
   `P(a, c) = 0`. ∎
