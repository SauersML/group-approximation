---
rg: 2
id: continued-fraction-real-realizes-every-turing-degree
kind: claim
title: Every set S of naturals is Turing equivalent to the irrational number [0; 1+χ_S(0), 1+χ_S(1), ...]
---

For `S ⊆ N` let

```text
α_S = [0; 1+χ_S(0), 1+χ_S(1), 1+χ_S(2), …]      (simple continued fraction).
```

Then `α_S` is an irrational number in `(0,1)`, and `α_S ≡_T S`.

So every Turing degree contains an irrational number in `(0,1)`. The computable degree is included, and the
choice is uniform in `S`. This replaces the two-case choice in
`every-turing-degree-is-a-simple-kazhdan-lef-word-problem-proof`: `√2−1` for degree 0, and a binary expansion
`0.1 b_0 1 b_1 …` otherwise.
