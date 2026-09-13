---
rg: 2
id: sturmian-language-is-turing-equivalent-to-angle
kind: claim
title: The language of the Sturmian subshift X_α is Turing equivalent to the irrational angle α
artifacts:
  - research/artifacts/un-open-5-word-problem-degrees-2026-09-13.md
---

For irrational `α ∈ (0,1)` and the Sturmian coding subshift `X_α` of `continuum-many-infinite-minimal-binary-subshifts`,
`L(X_α) ≡_T α`, where `α` stands for its binary expansion.

- From `L(X_α)`: every legal word of length `n` has `⌊nα⌋` or `⌊nα⌋+1` ones, so any legal word gives `α` to
  precision `1/n`.
- From `α`: the length-`n` codings are constant on the open gaps between the points `−tα mod 1`, `t ≤ n`. These
  gaps and a rational interior point of each are computable from `α`. So `L_n(X_α)` is a computable finite list.
