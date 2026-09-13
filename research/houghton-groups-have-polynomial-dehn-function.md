---
rg: 2
id: houghton-groups-have-polynomial-dehn-function
kind: claim
title: "For every n >= 3, Houghton's group H_n has a polynomially bounded Dehn function"
---

For every `n >= 3` there is an integer `d` with `δ_(H_n)(x) ≼ x^d`, for any
finite presentation of `H_n`.

S. R. Lee (arXiv:1212.0257, Theorem D) proves `δ_(H_n)(x) ≼ e^x`; this claim
asks for a polynomial improvement.

## Attempts

- 2026-09-13 (z1-24-houghton): reduction in progress. The translation part
  `Z^(n-1)` costs `O(x^2)`. Every null-homotopic word of length `x` becomes,
  after `O(x^2)` relator applications, a product of at most `O(x^2)`
  conjugates of the basic transposition `α` by words of length `<= x`. The
  symmetric-group word problem for a product of `M` transpositions on `m`
  points is solved with `O(M m)` applications of the transposition relations
  `τ^2 = 1`, `τ σ = σ τ^σ` (carry-and-merge elimination of one point at a
  time). So a polynomial bound follows once every such transposition relation
  between conjugates of `α` by words of length `O(x)` has polynomial area in
  `H_n`. That is the open crux.
