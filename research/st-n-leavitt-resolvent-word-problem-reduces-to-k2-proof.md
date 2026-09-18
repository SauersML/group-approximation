---
rg: 2
id: st-n-leavitt-resolvent-word-problem-reduces-to-k2-proof
kind: route
title: Decide the ring by simplicity, the matrix group by entries, and the Steinberg group by certifying nontrivial K_2 elements
target: st-n-leavitt-resolvent-word-problem-reduces-to-k2
requires:
  - leavitt-resolvent-ring-is-fp-simple-of-char-zero
  - steinberg-finite-presentation-and-kazhdan-theorem
---

**Item 1.**
- *The ring.* `R_L` is finitely presented, nonzero and simple.
  - For a word `w` in the ring generators, `w = 0` is recursively enumerable, from the presentation.
  - If `w ≠ 0`, simplicity gives `1 = Σ a_i w b_i` for some words `a_i`, `b_i`. So `w ≠ 0` is recursively
    enumerable, and it is exactly `1 ∈ (w)`, because `R_L ≠ 0`.
  - Running both searches decides `w = 0`.
- *The matrix group.*
  - The `e_ij(g)` generate `E_N(R_L)` for `N >= 3`, since `e_ij(a)e_ij(b) = e_ij(a+b)` and `[e_ij(a), e_jk(b)] = e_ik(ab)`.
  - A word in them evaluates to a `N × N` matrix whose entries are ring words, computed by the matrix product
    rule.
  - It is `1` exactly when each diagonal entry minus `1` and each off-diagonal entry is `0`, which the ring's word
    problem decides. ∎

**Item 2.**
- `St_N(R_L)` is finitely presented for `N >= 4` (`steinberg-finite-presentation-and-kazhdan-theorem`). Its generators
  `x_ij(g)` map to the `e_ij(g)` above.
- By item 1, deciding whether a word maps to `1` in `E_N(R_L)` is decidable.
- If it does not, the word is nontrivial. If it does, the word lies in `K_2(N,R_L)`. Its triviality is recursively
  enumerable by the presentation, and its nontriviality is recursively enumerable by hypothesis. ∎

**Item 3.**
- Under (i), a word `v` in `K_2(N,R_L)` is trivial if and only if its stable image is trivial. Under (ii), that holds
  if and only if `ι(v) = 1` in `H`, which is decidable.
- If `K_2(R_L) = 0`, (i) forces `K_2(N,R_L) = 0`, so `St_N(R_L) = E_N(R_L)`, which is decided by item 1. ∎
