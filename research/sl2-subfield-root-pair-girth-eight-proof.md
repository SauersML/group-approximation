---
rg: 2
id: sl2-subfield-root-pair-girth-eight-proof
kind: route
title: Splitting F_q^2 as F_q plus sF_q kills relations of syllable length 3 and 4 between u(F_q) and v(sF_q)
target: sl2-subfield-root-pair-girth-eight
requires: []
---

**Cycles are relations.** In `Γ_A(E, E')`, the edges at `gE` are the elements `ge` with `e ∈ E`, and the
edge `ge` ends at `geE'`.
- A non-backtracking closed walk of length `2m` from `E` has edges
  `x_1, x_1y_1, x_1y_1x_2, …, x_1y_1⋯x_my_m`, with `y_i ∈ E' \ 1` and `x_2, …, x_m ∈ E \ 1`.
- It closes iff `w = y_1x_2⋯x_my_m ∈ E`, and its last edge differs from its first iff `w ≠ 1`.
- So it gives `x' y_1 x_2 y_2 ⋯ x_m y_m = 1` with `x' = w^{-1} ∈ E \ 1`: an alternating word of syllable
  length `m`, every letter nontrivial, equal to `1`.
- Conversely such a relation gives such a walk.

A shortest non-backtracking closed walk is a cycle, so the girth is `2m_0`, where `m_0` is the least
syllable length of such a relation.

**Letters.** In characteristic 2 every letter is an involution, and

```text
u(a)v(b) = [[1+ab, a], [b, 1]],        v(b)u(a) = [[1, a], [b, 1+ab]],
u(a_1)v(b_1)u(a_2)v(b_2) = [[(1+a_1b_1)(1+a_2b_2) + a_1b_2,  (1+a_1b_1)a_2 + a_1], [ … , a_2b_1 + 1]].
```

Throughout, `a_i ∈ k \ 0` and `b_i = sβ_i` with `β_i ∈ k \ 0`.

**m = 1.** `xy = 1` forces `x = y^{-1} ∈ E ∩ E' ⊆ U_+ ∩ U_- = 1`. This also proves (a).

**m = 2.** The relation is `u(a_1)v(b_1) = v(b_2)u(a_2)`. The `(1,1)` entries give `a_1b_1 = 0`, which is
impossible. This uses only `E ⊆ U_+`, `E' ⊆ U_-` and characteristic 2, and proves (c).

**m = 3.** The relation is `u(a_1)v(b_1)u(a_2)v(b_2) = v(b_3)u(a_3)`. Comparing `(1,2)` entries gives
`a_1 a_2 b_1 = a_1 + a_2 + a_3`.
- The left side lies in `sk \ 0`; the right side lies in `k`.
- `sk ∩ k = 0` because `s ∉ k`, a contradiction.

**m = 4.** The relation is `u(a_1)v(b_1)u(a_2)v(b_2) = v(b_4)u(a_4)v(b_3)u(a_3)`.
- The `(1,1)` entry of the right side is `1 + a_4b_3`. That of the left side is
  `1 + a_1b_1 + a_2b_2 + a_1b_2 + a_1a_2b_1b_2`.
- Let `X^2 + tX + ν` be the minimal polynomial of `s` over `k`, so `s^2 = ts + ν` with
  `ν = s^{q+1} ≠ 0`. As a `k`-vector space, `F = k ⊕ sk`.
- The difference of the two entries is `s(a_1β_1 + a_2β_2 + a_1β_2 + a_4β_3 + t a_1a_2β_1β_2)` plus
  `ν a_1a_2β_1β_2`.
- Its `k`-component `ν a_1a_2β_1β_2` is nonzero, so the entries differ, a contradiction.

So `m_0 >= 5`, and the girth is at least `10`, which proves (b). ∎
