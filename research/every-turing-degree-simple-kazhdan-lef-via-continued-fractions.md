---
rg: 2
id: every-turing-degree-simple-kazhdan-lef-via-continued-fractions
kind: route
title: One uniform irrational slope per degree by continued fractions, then word problem ≡ language ≡ slope
target: every-turing-degree-is-a-simple-kazhdan-lef-word-problem
requires: [continued-fraction-real-realizes-every-turing-degree, subshift-elementary-group-word-problem-equals-language, sturmian-language-is-turing-equivalent-to-angle, simple-kazhdan-lef-group-from-minimal-subshift]
artifacts:
  - research/artifacts/sk-word-problem-proposal-2026-09-13.md
---

1. **Slope.** Given a Turing degree `d`, pick `S ∈ d` and set `α = α_S = [0; 1+χ_S(0), 1+χ_S(1), …]`. It is irrational
   and `α ≡_T S` (`continued-fraction-real-realizes-every-turing-degree`). No case split for `d = 0` is needed.
2. **Degree.** The word problem of `S_(X_α)` is `≡_T L(X_α)` (`subshift-elementary-group-word-problem-equals-language`),
   which is `≡_T α` (`sturmian-language-is-turing-equivalent-to-angle`), which is `≡_T S`.
3. **Properties.** `S_(X_α)` is infinite, finitely generated, simple, Kazhdan and LEF
   (`simple-kazhdan-lef-group-from-minimal-subshift`).
4. **Invariance.** The degree of the word problem does not depend on the finite generating set. So groups with
   different degrees are nonisomorphic, and there are continuum many pairwise nonisomorphic `S_(X_α)`.

The proposed text of the note's word-problem section follows this route (artifact). It also proves the balance
count inline: `c(y)_[0,n)` has `⌊y + nα⌋` ones, since `⌊y+(t+1)α⌋ − ⌊y+tα⌋ = 1` exactly when
`y + tα mod 1 ≥ 1−α`.
