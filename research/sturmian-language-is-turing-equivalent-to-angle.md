---
rg: 2
id: sturmian-language-is-turing-equivalent-to-angle
kind: claim
title: The language of the Sturmian subshift X_α is Turing equivalent to the irrational angle α
distinct_from:
  subshift-elementary-group-word-problem-degree: that already records L(X_α) ≡_T α, by balance and the circle partition; this isolates it as its own node.
artifacts:
  - research/artifacts/un-open-5-word-problem-degrees-2026-09-13.md
---

For irrational `α ∈ (0,1)` and the Sturmian coding subshift `X_α` of `continuum-many-infinite-minimal-binary-subshifts`,
`L(X_α) ≡_T α`, where `α` stands for its binary expansion.

- From `L(X_α)`: every legal word of length `n` has `⌊nα⌋` or `⌊nα⌋+1` ones, so any legal word gives `α` to
  precision `1/n`.
- From `α`: the length-`n` codings are constant on the open gaps between the points `−tα mod 1`, `t ≤ n`. These
  gaps and a rational interior point of each are computable from `α`. So `L_n(X_α)` is a computable finite list.

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part1.md` §1.4): PASS,
folklore.** Both directions were re-derived (the boundary points `y = p_t`, `y = p_(t+1)` and the gap codings).
The statement is classical for Sturmian words and is already stated on main (`distinct_from`).
