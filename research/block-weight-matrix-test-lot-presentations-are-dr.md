---
rg: 2
id: block-weight-matrix-test-lot-presentations-are-dr
kind: claim
title: The Barmak--Minian block I-test certifies diagrammatic reducibility, hence asphericity, of a presentation
distinct_from:
  adian-lots-with-acyclic-initial-or-terminal-graph-are-dr: that is Gersten's acyclic left/right graph criterion; this is the weight-matrix I-test in block form, which strictly generalizes it and covers deforestable and weakly deforestable LOGs.
---

Let `P = <x_1..x_n | r_1..r_m>` present `G`. For `v ∈ R^n` orthogonal to every
exponent vector `q(r_j)`, the weight of a word `w` is `<q(w), v>`, and the weight
matrix `M(v)` has entries the families `M_{i,j} = {weight of s(k, r_j)}` over the
occurrences `k` of `x_i` in `r_j`, where `s(k, w)` is the suffix starting at
letter `k` if that letter is positive and at letter `k+1` if negative. A matrix
of families is *good* if it has at least as many rows as columns and there are an
ordering `j_1..j_m` of the columns and distinct rows `i_1..i_m` with, for each
`k`: `M_{i_k,j_k}` nonempty, its maximum `λ_k` is the maximum of the whole row,
and `λ_k` has multiplicity one in `M_{i_k,j_k} ∪ ... ∪ M_{i_k,j_m}`.

**Statement.** Suppose `1 <= n_1 < ... < n_k = n` and `1 <= m_1 < ... < m_k = m`
are such that `r_1..r_{m_l}` are words in `x_1..x_{n_l}` for each `l`, and there
are `v_1..v_k`, each orthogonal to every `q(r_j)`, with each block `M_l(v_l)`
(rows `n_{l-1}+1..n_l`, columns `m_{l-1}+1..m_l`) good. Then `K(P)` is
diagrammatically reducible, hence aspherical. The case `k = 1` is the I-test.

Imported; see `block-weight-matrix-test-citation`.

_Orphan sweep (2026-09-14): this node cited `research/artifacts/hl-whitehead-relative-pins-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._
