---
rg: 2
id: every-turing-degree-is-a-simple-kazhdan-lef-word-problem-proof
kind: route
title: Choose an irrational angle in the degree, then word problem ≡ language ≡ angle
target: every-turing-degree-is-a-simple-kazhdan-lef-word-problem
requires: [subshift-elementary-group-word-problem-equals-language, sturmian-language-is-turing-equivalent-to-angle, simple-kazhdan-lef-group-from-minimal-subshift]
artifacts:
  - research/artifacts/un-open-5-word-problem-degrees-2026-09-13.md
---

Artifact §3.
1. **Choosing `α`.** For `d = 0` take `α = √2−1`. Otherwise pick `B ∈ d` and set
   `α = 0.1 b_0 1 b_1 1 b_2 …` in binary, with `b_i = [i ∈ B]`. The expansion is not eventually periodic, since
   `B` is not computable, so `α` is irrational, and `α ≡_T B`.
2. **Degree.** The word problem of `S_(X_α)` ≡_T `L(X_α)` (`subshift-elementary-group-word-problem-equals-language`)
   ≡_T `α` (`sturmian-language-is-turing-equivalent-to-angle`), which lies in `d`.
3. **Properties.** `S_(X_α)` is infinite, finitely generated, simple, Kazhdan and LEF
   (`simple-kazhdan-lef-group-from-minimal-subshift`).
4. **Invariance.** A change of finite generating set is a computable translation of words, so the word-problem
   degree is an isomorphism invariant.
