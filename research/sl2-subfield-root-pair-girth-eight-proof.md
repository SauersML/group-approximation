---
rg: 2
id: sl2-subfield-root-pair-girth-eight-proof
kind: route
title: A 6-cycle would force a1 a2 b1 into F_q while it lies in sF_q, so no relation of syllable length 3 exists
target: sl2-subfield-root-pair-girth-eight
requires: []
---

**Cycles are relations.** In `Γ_A(E, E')`, the edges at `gE` are the elements `ge`, `e ∈ E`, and the edge
`ge` ends at `geE'`.
- A non-backtracking closed walk of length `2m` from `E` has edges
  `x_1, x_1y_1, x_1y_1x_2, …, x_1y_1⋯x_my_m`, with `y_i ∈ E' \ 1` and `x_2, …, x_m ∈ E \ 1`.
- It closes iff `w = y_1x_2⋯x_my_m ∈ E`. The last edge differs from the first iff `w ≠ 1`.
- So it gives `x' y_1 x_2 y_2 ⋯ x_m y_m = 1` with `x' = w^{-1} ∈ E \ 1`: an alternating word of syllable
  length `m`, with every letter nontrivial, equal to `1`.
- Conversely such a relation gives a closed non-backtracking walk of length `2m`.

A shortest non-backtracking closed walk is a cycle. So the girth is `2m_0`, where `m_0` is the least
syllable length of such a relation.

**Letters.** In characteristic 2 every letter is an involution, and

```text
u(a)v(b) = [[1+ab, a], [b, 1]],        v(b)u(a) = [[1, a], [b, 1+ab]].
```

**m = 1.** `xy = 1` forces `x = y^{-1} ∈ E ∩ E' ⊆ U_+ ∩ U_- = 1`. This also proves (a).

**m = 2.** `u(a_1)v(b_1)u(a_2)v(b_2) = 1` iff `u(a_1)v(b_1) = v(b_2)u(a_2)`. Comparing `(1,1)` entries
gives `a_1 b_1 = 0`, which is impossible. This uses only `E ⊆ U_+`, `E' ⊆ U_-` and characteristic 2, and
proves (c).

**m = 3.** The relation `u(a_1)v(b_1)u(a_2)v(b_2)u(a_3)v(b_3) = 1` is equivalent to

```text
u(a_1)v(b_1)u(a_2)v(b_2) = v(b_3)u(a_3).
```

The `(1,2)` entry of the left side is `(1 + a_1b_1)a_2 + a_1`, and that of the right side is `a_3`. So
`a_1 a_2 b_1 = a_1 + a_2 + a_3`.
- With `a_i ∈ k \ 0` and `b_1 ∈ sk \ 0`, the left side lies in `sk \ 0`.
- The right side lies in `k`.
- `sk ∩ k = 0` because `s ∉ k`.

This is a contradiction. So `m_0 >= 4` and the girth is at least `8`, which proves (b). ∎
